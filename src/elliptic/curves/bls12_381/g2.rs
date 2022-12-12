/*
    This file is part of Curv library
    Copyright 2018 by Kzen Networks
    (https://github.com/KZen-networks/curv)
    License MIT: <https://github.com/KZen-networks/curv/blob/master/LICENSE>
*/

use std::fmt;

use ff_zeroize::{PrimeField, ScalarEngine};
use generic_array::GenericArray;
use pairing_plus::bls12_381::{G2Compressed, G2Uncompressed, G2};
use pairing_plus::hash_to_curve::HashToCurve;
use pairing_plus::hash_to_field::ExpandMsgXmd;
use pairing_plus::{CurveAffine, CurveProjective, Engine};
use pairing_plus::{EncodedPoint, SubgroupCheck};
use zeroize::Zeroize;

use crate::arithmetic::*;
use crate::elliptic::curves::traits::*;

use super::scalar::FieldScalar;

lazy_static::lazy_static! {
    static ref GENERATOR: G2Point = G2Point {
        purpose: "generator",
        ge: PK::one(),
    };

    static ref BASE_POINT2: G2Point = {
        const BASE_POINT2: [u8; 192] = [
            10, 171, 191, 0, 165, 128, 154, 219, 38, 59, 180, 198, 223, 124, 148, 112, 212, 13, 121,
            116, 67, 51, 69, 225, 123, 58, 65, 247, 156, 59, 136, 127, 69, 195, 145, 42, 129, 183,
            180, 24, 133, 235, 91, 7, 8, 124, 159, 252, 12, 127, 52, 139, 183, 175, 115, 201, 98,
            117, 239, 5, 116, 244, 30, 150, 215, 90, 75, 40, 43, 154, 34, 140, 116, 245, 205, 90,
            220, 100, 102, 223, 78, 183, 184, 218, 235, 225, 202, 36, 15, 111, 170, 6, 172, 81, 126,
            81, 12, 152, 225, 206, 104, 117, 104, 117, 192, 83, 226, 193, 223, 117, 136, 3, 86, 37,
            33, 84, 159, 218, 122, 29, 245, 222, 52, 17, 136, 82, 60, 224, 174, 55, 210, 63, 163,
            136, 8, 162, 196, 226, 13, 134, 142, 254, 149, 231, 12, 212, 187, 122, 205, 1, 14, 82,
            30, 254, 55, 188, 248, 119, 91, 122, 89, 184, 151, 106, 209, 15, 63, 178, 4, 71, 17,
            156, 195, 3, 58, 72, 212, 27, 84, 79, 252, 133, 68, 160, 240, 188, 95, 162, 172, 87,
            115, 19,
        ];

        let mut point = G2Uncompressed::empty();
        point.as_mut().copy_from_slice(&BASE_POINT2);
        G2Point {
            purpose: "base_point2",
            ge: point.into_affine().expect("invalid base_point"),
        }
    };
}

pub const SECRET_KEY_SIZE: usize = 32;
pub const COMPRESSED_SIZE: usize = 96;

pub type SK = <pairing_plus::bls12_381::Bls12 as ScalarEngine>::Fr;
pub type PK = <pairing_plus::bls12_381::Bls12 as Engine>::G2Affine;

/// Bls12-381-2 (G2) curve implementation based on [pairing_plus] library
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Bls12_381_2 {}

#[derive(Clone, Copy)]
pub struct G2Point {
    purpose: &'static str,
    ge: PK,
}

pub type GE2 = G2Point;

impl Curve for Bls12_381_2 {
    type Point = GE2;
    type Scalar = FieldScalar;

    const CURVE_NAME: &'static str = "bls12_381_1";
}

impl ECPoint for G2Point {
    type Scalar = FieldScalar;
    type Underlying = PK;

    type CompressedPointLength = typenum::U96;
    type UncompressedPointLength = typenum::U192;

    fn zero() -> G2Point {
        G2Point {
            purpose: "zero",
            ge: PK::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.ge.is_zero()
    }

    fn generator() -> &'static G2Point {
        &GENERATOR
    }

    fn base_point2() -> &'static G2Point {
        &BASE_POINT2
    }

    fn from_coords(x: &BigInt, y: &BigInt) -> Result<G2Point, NotOnCurve> {
        let vec_x = x.to_bytes();
        let vec_y = y.to_bytes();
        if vec_x.len() > COMPRESSED_SIZE || vec_y.len() > COMPRESSED_SIZE {
            return Err(NotOnCurve);
        }
        let mut uncompressed = [0u8; 2 * COMPRESSED_SIZE];
        uncompressed[COMPRESSED_SIZE - vec_x.len()..COMPRESSED_SIZE].copy_from_slice(&vec_x);
        uncompressed[(2 * COMPRESSED_SIZE) - vec_y.len()..].copy_from_slice(&vec_y);
        debug_assert_eq!(x, &BigInt::from_bytes(&uncompressed[..COMPRESSED_SIZE]));
        debug_assert_eq!(y, &BigInt::from_bytes(&uncompressed[COMPRESSED_SIZE..]));

        let mut point = G2Uncompressed::empty();
        point.as_mut().copy_from_slice(&uncompressed);

        Ok(G2Point {
            purpose: "from_coords",
            ge: point.into_affine().map_err(|_| NotOnCurve)?,
        })
    }

    fn x_coord(&self) -> Option<BigInt> {
        if self.is_zero() {
            None
        } else {
            let uncompressed = G2Uncompressed::from_affine(self.ge);
            let x_coord = &uncompressed.as_ref()[0..COMPRESSED_SIZE];
            let bn = BigInt::from_bytes(x_coord);
            Some(bn)
        }
    }

    fn y_coord(&self) -> Option<BigInt> {
        if self.is_zero() {
            None
        } else {
            let uncompressed = G2Uncompressed::from_affine(self.ge);
            let y_coord = &uncompressed.as_ref()[COMPRESSED_SIZE..COMPRESSED_SIZE * 2];
            let bn = BigInt::from_bytes(y_coord);
            Some(bn)
        }
    }

    fn coords(&self) -> Option<PointCoords> {
        if self.is_zero() {
            None
        } else {
            let uncompressed = G2Uncompressed::from_affine(self.ge);
            let x = &uncompressed.as_ref()[0..COMPRESSED_SIZE];
            let y = &uncompressed.as_ref()[COMPRESSED_SIZE..COMPRESSED_SIZE * 2];
            let x = BigInt::from_bytes(x);
            let y = BigInt::from_bytes(y);
            Some(PointCoords { x, y })
        }
    }

    fn serialize_compressed(&self) -> GenericArray<u8, Self::CompressedPointLength> {
        *GenericArray::from_slice(G2Compressed::from_affine(self.ge).as_ref())
    }

    fn serialize_uncompressed(&self) -> GenericArray<u8, Self::UncompressedPointLength> {
        *GenericArray::from_slice(G2Uncompressed::from_affine(self.ge).as_ref())
    }

    fn deserialize(bytes: &[u8]) -> Result<G2Point, DeserializationError> {
        if bytes.len() == COMPRESSED_SIZE {
            let mut compressed = G2Compressed::empty();
            compressed.as_mut().copy_from_slice(bytes);
            Ok(G2Point {
                purpose: "deserialize",
                ge: compressed.into_affine().map_err(|_| DeserializationError)?,
            })
        } else if bytes.len() == 2 * COMPRESSED_SIZE {
            let mut uncompressed = G2Uncompressed::empty();
            uncompressed.as_mut().copy_from_slice(bytes);
            Ok(G2Point {
                purpose: "deserialize",
                ge: uncompressed
                    .into_affine()
                    .map_err(|_| DeserializationError)?,
            })
        } else {
            Err(DeserializationError)
        }
    }

    fn check_point_order_equals_group_order(&self) -> bool {
        !self.is_zero() && self.ge.in_subgroup()
    }

    fn scalar_mul(&self, scalar: &Self::Scalar) -> G2Point {
        let result = self.ge.mul(scalar.underlying_ref().into_repr());
        G2Point {
            purpose: "scalar_mul",
            ge: result.into_affine(),
        }
    }

    fn add_point(&self, other: &Self) -> G2Point {
        let mut result = G2::from(self.ge);
        result.add_assign_mixed(&other.ge);
        G2Point {
            purpose: "add_point",
            ge: result.into_affine(),
        }
    }

    fn sub_point(&self, other: &Self) -> G2Point {
        let mut result = G2::from(self.ge);
        result.sub_assign_mixed(&other.ge);
        G2Point {
            purpose: "sub_point",
            ge: result.into_affine(),
        }
    }

    fn neg_point(&self) -> Self {
        let mut result = self.ge;
        result.negate();
        G2Point {
            purpose: "neg",
            ge: result,
        }
    }

    fn neg_point_assign(&mut self) {
        self.ge.negate();
    }

    fn underlying_ref(&self) -> &Self::Underlying {
        &self.ge
    }
    fn underlying_mut(&mut self) -> &mut Self::Underlying {
        &mut self.ge
    }
    fn from_underlying(ge: Self::Underlying) -> G2Point {
        G2Point {
            purpose: "from_underlying",
            ge,
        }
    }
}

impl G2Point {
    /// Converts message to G1 point.
    ///
    /// Uses [expand_message_xmd][xmd] based on sha256.
    ///
    /// [xmd]: https://www.ietf.org/id/draft-irtf-cfrg-hash-to-curve-10.html#name-expand_message_xmd-2
    pub fn hash_to_curve(message: &[u8]) -> Self {
        let cs = &[1u8];
        let point = <G2 as HashToCurve<ExpandMsgXmd<old_sha2::Sha256>>>::hash_to_curve(message, cs);
        G2Point {
            purpose: "hash_to_curve",
            ge: point.into_affine(),
        }
    }
}

impl fmt::Debug for G2Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Point {{ purpose: {:?}, uncompressed: {:?} }}",
            self.purpose,
            hex::encode(self.serialize_uncompressed()),
        )
    }
}

impl PartialEq for G2Point {
    fn eq(&self, other: &G2Point) -> bool {
        self.ge == other.ge
    }
}

impl Zeroize for G2Point {
    fn zeroize(&mut self) {
        self.ge.zeroize()
    }
}

#[cfg(test)]
mod tests {
    use pairing_plus::{bls12_381::G2Uncompressed, CurveProjective, EncodedPoint, SubgroupCheck};

    use crate::elliptic::curves::ECPoint;

    use super::{ExpandMsgXmd, G2Point, HashToCurve, G2};

    #[test]
    fn base_point2_nothing_up_my_sleeve() {
        // Generate base_point2
        let cs = &[1u8];
        let msg = &[1u8];
        let point = <G2 as HashToCurve<ExpandMsgXmd<old_sha2::Sha256>>>::hash_to_curve(msg, cs)
            .into_affine();
        assert!(point.in_subgroup());

        // Print in uncompressed form
        let point_uncompressed = G2Uncompressed::from_affine(point);
        println!("Uncompressed base_point2: {:?}", point_uncompressed);

        // Check that ECPoint::base_point2() returns generated point
        let base_point2: &G2Point = ECPoint::base_point2();
        assert_eq!(point, base_point2.ge);
    }
}
