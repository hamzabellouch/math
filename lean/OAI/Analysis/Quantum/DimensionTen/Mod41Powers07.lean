import OAI.Analysis.Quantum.DimensionTen.Mod41Powers06

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow13_2 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (7 + z * (4 + z * (21 + z * (9 + z * (21 + z * (15 + z * (6 + z * (8 + z * (13 + z * (37 + z * (8 + z * (9 + z * (3 + z * (24 + z * (11 + z * (26 + z * (8 + z * (35 + z * 18)))))))))))))))))))

def pow13_2_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (8 + z * (29 + z * (37 + z * (15 + z * (40 + z * (36 + z * (32 + z * (29 + z * (0 + z * (20 + z * (39 + z * (19 + z * (22 + z * (3 + z * (0 + z * (39 + z * (32 + z * 10))))))))))))))))))

def pow13_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * ((-6) + z * ((-26) + z * ((-37) + z * ((-28) + z * ((-32) + z * ((-29) + z * ((-49) + z * ((-6) + z * ((-6) + z * ((-33) + z * ((-26) + z * ((-28) + z * ((-25) + z * (19 + z * ((-14) + z * ((-8) + z * ((-70) + z * ((-40) + z * ((-22) + z * ((-3) + z * ((-27) + z * ((-9) + z * ((-30) + z * (0 + z * ((-45) + z * (27 + z * ((-41) + z * (25 + z * ((-1) + z * (5 + z * ((-18) + z * ((-13) + z * ((-11) + z * (24 + z * ((-24) + z * (16 + z * ((-2) + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow13_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z + (41 : R) * pow13_2_mul_t z := by
  simp only [u12, pow13_2_q, f, pow13_2, pow13_2_mul_t]
  simp only [pow12_41]
  ring

theorem pow13_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_2_mul_integer z


theorem pow13_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z * u12 z = pow13_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_2_mul z


theorem pow13_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 2 = pow13_2 z := by
  calc
    _ = u12 z ^ 1 * u12 z ^ 1 := by ring
    _ = u12 z * u12 z := by simp only [pow_one]
    _ = _ := pow13_2_root z hz


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (17 + z * (26 + z * (40 + z * (18 + z * (13 + z * (17 + z * (16 + z * (37 + z * (8 + z * (13 + z * (34 + z * (18 + z * (16 + z * (6 + z * (18 + z * (11 + z * (20 + z * (21 + z * 29)))))))))))))))))))

def pow13_4_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (38 + z * (16 + z * (12 + z * (33 + z * (26 + z * (17 + z * (11 + z * (21 + z * (38 + z * (14 + z * (19 + z * (0 + z * (35 + z * (12 + z * (16 + z * (33 + z * (27 + z * 37))))))))))))))))))

def pow13_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-33) + z * ((-35) + z * ((-24) + z * ((-44) + z * ((-48) + z * ((-32) + z * ((-38) + z * ((-67) + z * ((-69) + z * ((-28) + z * ((-77) + z * ((-70) + z * ((-82) + z * ((-37) + z * ((-87) + z * ((-107) + z * ((-128) + z * ((-118) + z * ((-72) + z * ((-129) + z * ((-60) + z * ((-67) + z * ((-74) + z * ((-59) + z * ((-89) + z * ((-40) + z * ((-66) + z * ((-26) + z * ((-44) + z * ((-38) + z * ((-50) + z * ((-48) + z * ((-39) + z * ((-15) + z * ((-20) + z * (1 + z * (3 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow13_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z + (41 : R) * pow13_4_mul_t z := by
  simp only [pow13_2, pow13_4_q, f, pow13_4, pow13_4_mul_t]
  
  ring

theorem pow13_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_4_mul_integer z


theorem pow13_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_2 z * pow13_2 z = pow13_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_4_mul z


theorem pow13_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 4 = pow13_4 z := by
  calc
    _ = u12 z ^ 2 * u12 z ^ 2 := by ring
    _ = pow13_2 z * pow13_2 z := by rw [pow13_2_pow z hz]
    _ = _ := pow13_4_root z hz


def pow13_5 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (11 + z * (39 + z * (36 + z * (26 + z * (0 + z * (12 + z * (37 + z * (11 + z * (26 + z * (30 + z * (17 + z * (28 + z * (19 + z * (4 + z * (1 + z * (15 + z * (3 + z * (40 + z * 38)))))))))))))))))))

def pow13_5_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (4 + z * (17 + z * (7 + z * (22 + z * (31 + z * (38 + z * (21 + z * (25 + z * (23 + z * (32 + z * (3 + z * (6 + z * (17 + z * (26 + z * (35 + z * (0 + z * (35 + z * 28))))))))))))))))))

def pow13_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-9) + z * ((-25) + z * (2 + z * ((-23) + z * ((-1) + z * ((-7) + z * ((-1) + z * ((-8) + z * ((-22) + z * ((-24) + z * (7 + z * (33 + z * (21 + z * ((-17) + z * ((-11) + z * ((-7) + z * ((-44) + z * ((-8) + z * ((-31) + z * (22 + z * ((-28) + z * ((-3) + z * (6 + z * ((-42) + z * ((-58) + z * ((-17) + z * (10 + z * (5 + z * ((-35) + z * (6 + z * ((-26) + z * ((-30) + z * ((-40) + z * ((-14) + z * (5 + z * (3 + z * ((-5) + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow13_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_4 z * u12 z = pow13_5_q z * f z + pow13_5 z + (41 : R) * pow13_5_mul_t z := by
  simp only [pow13_4, u12, pow13_5_q, f, pow13_5, pow13_5_mul_t]
  simp only [pow12_41]
  ring

theorem pow13_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_4 z * u12 z = pow13_5_q z * f z + pow13_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_5_mul_integer z


theorem pow13_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_4 z * u12 z = pow13_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_5_mul z


theorem pow13_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 5 = pow13_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow13_4_pow z hz]
  exact pow13_5_root z hz


def pow13_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (15 + z * (18 + z * (2 + z * (12 + z * (21 + z * (5 + z * (27 + z * (23 + z * (32 + z * (37 + z * (16 + z * (15 + z * (20 + z * (23 + z * (29 + z * (18 + z * (4 + z * (12 + z * 40)))))))))))))))))))

def pow13_10_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (19 + z * (9 + z * (20 + z * (23 + z * (5 + z * (4 + z * (21 + z * (29 + z * (21 + z * (4 + z * (17 + z * (29 + z * (28 + z * (22 + z * (14 + z * (1 + z * (23 + z * 9))))))))))))))))))

def pow13_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-6) + z * (36 + z * (44 + z * (48 + z * (38 + z * (68 + z * (53 + z * ((-5) + z * (66 + z * (93 + z * (56 + z * (69 + z * (82 + z * (58 + z * ((-2) + z * (29 + z * ((-18) + z * (35 + z * (52 + z * (79 + z * (97 + z * (68 + z * (3 + z * ((-48) + z * (32 + z * (22 + z * ((-16) + z * (19 + z * (15 + z * (14 + z * (17 + z * ((-16) + z * ((-38) + z * (0 + z * (18 + z * (24 + z * (67 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow13_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_5 z * pow13_5 z = pow13_10_q z * f z + pow13_10 z + (41 : R) * pow13_10_mul_t z := by
  simp only [pow13_5, pow13_10_q, f, pow13_10, pow13_10_mul_t]
  
  ring

theorem pow13_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_5 z * pow13_5 z = pow13_10_q z * f z + pow13_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_10_mul_integer z


theorem pow13_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_5 z * pow13_5 z = pow13_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_10_mul z


theorem pow13_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 10 = pow13_10 z := by
  calc
    _ = u12 z ^ 5 * u12 z ^ 5 := by ring
    _ = pow13_5 z * pow13_5 z := by rw [pow13_5_pow z hz]
    _ = _ := pow13_10_root z hz


def pow13_20 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (10 + z * (38 + z * (33 + z * (33 + z * (15 + z * (28 + z * (16 + z * (30 + z * (23 + z * (31 + z * (17 + z * (13 + z * (3 + z * (4 + z * (22 + z * (26 + z * (0 + z * (37 + z * 28)))))))))))))))))))

def pow13_20_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (0 + z * (36 + z * (20 + z * (27 + z * (26 + z * (24 + z * (23 + z * (7 + z * (31 + z * (14 + z * (11 + z * (40 + z * (27 + z * (14 + z * (35 + z * (17 + z * (28 + z * 1))))))))))))))))))

def pow13_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-8) + z * ((-49) + z * ((-17) + z * ((-73) + z * ((-36) + z * ((-52) + z * ((-67) + z * ((-39) + z * ((-49) + z * ((-29) + z * ((-45) + z * ((-31) + z * ((-68) + z * ((-49) + z * ((-37) + z * ((-60) + z * ((-57) + z * ((-24) + z * ((-59) + z * (3 + z * ((-23) + z * ((-17) + z * (7 + z * (12 + z * (9 + z * (21 + z * (4 + z * (9 + z * (28 + z * ((-13) + z * ((-38) + z * ((-19) + z * (7 + z * (18 + z * (12 + z * ((-10) + z * (22 + z * 39))))))))))))))))))))))))))))))))))))))

theorem pow13_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_10 z * pow13_10 z = pow13_20_q z * f z + pow13_20 z + (41 : R) * pow13_20_mul_t z := by
  simp only [pow13_10, pow13_20_q, f, pow13_20, pow13_20_mul_t]
  
  ring

theorem pow13_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_10 z * pow13_10 z = pow13_20_q z * f z + pow13_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_20_mul_integer z


theorem pow13_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_10 z * pow13_10 z = pow13_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_20_mul z


theorem pow13_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 20 = pow13_20 z := by
  calc
    _ = u12 z ^ 10 * u12 z ^ 10 := by ring
    _ = pow13_10 z * pow13_10 z := by rw [pow13_10_pow z hz]
    _ = _ := pow13_20_root z hz


def pow13_40 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (9 + z * (25 + z * (3 + z * (6 + z * (37 + z * (40 + z * (17 + z * (3 + z * (31 + z * (13 + z * (6 + z * (20 + z * (4 + z * (11 + z * (29 + z * (32 + z * (4 + z * (36 + z * 27)))))))))))))))))))

def pow13_40_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (0 + z * (25 + z * (27 + z * (10 + z * (19 + z * (35 + z * (21 + z * (22 + z * (36 + z * (20 + z * (15 + z * (5 + z * (21 + z * (33 + z * (21 + z * (40 + z * (36 + z * 5))))))))))))))))))

def pow13_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-11) + z * ((-45) + z * ((-14) + z * ((-11) + z * (32 + z * (29 + z * ((-1) + z * (30 + z * (12 + z * (21 + z * (31 + z * (88 + z * (31 + z * (14 + z * ((-22) + z * ((-58) + z * ((-62) + z * ((-28) + z * ((-19) + z * (29 + z * (6 + z * (24 + z * ((-22) + z * ((-42) + z * ((-41) + z * (1 + z * ((-11) + z * ((-25) + z * ((-25) + z * ((-39) + z * ((-55) + z * ((-80) + z * ((-44) + z * (20 + z * ((-12) + z * (4 + z * (46 + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow13_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_20 z * pow13_20 z = pow13_40_q z * f z + pow13_40 z + (41 : R) * pow13_40_mul_t z := by
  simp only [pow13_20, pow13_40_q, f, pow13_40, pow13_40_mul_t]
  
  ring

theorem pow13_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_20 z * pow13_20 z = pow13_40_q z * f z + pow13_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_40_mul_integer z


theorem pow13_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_20 z * pow13_20 z = pow13_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_40_mul z


theorem pow13_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 40 = pow13_40 z := by
  calc
    _ = u12 z ^ 20 * u12 z ^ 20 := by ring
    _ = pow13_20 z * pow13_20 z := by rw [pow13_20_pow z hz]
    _ = _ := pow13_40_root z hz


def pow13_41 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (23 + z * (8 + z * (32 + z * (34 + z * (36 + z * (32 + z * (30 + z * (33 + z * (23 + z * (36 + z * (1 + z * (27 + z * (2 + z * (6 + z * (12 + z * (14 + z * (15 + z * (1 + z * 4)))))))))))))))))))

def pow13_41_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (28 + z * (4 + z * (23 + z * (3 + z * (40 + z * (33 + z * (25 + z * (4 + z * (33 + z * (28 + z * (22 + z * (5 + z * (26 + z * (11 + z * (25 + z * (17 + z * (14 + z * 19))))))))))))))))))

def pow13_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-22) + z * ((-5) + z * ((-29) + z * (3 + z * ((-44) + z * (0 + z * ((-26) + z * ((-17) + z * ((-13) + z * (7 + z * (1 + z * ((-15) + z * ((-34) + z * ((-6) + z * ((-15) + z * ((-4) + z * ((-53) + z * ((-33) + z * (26 + z * ((-20) + z * ((-2) + z * ((-14) + z * (33 + z * ((-19) + z * ((-24) + z * ((-12) + z * (1 + z * ((-4) + z * ((-2) + z * ((-8) + z * (5 + z * ((-10) + z * (17 + z * (4 + z * (30 + z * (12 + z * (11 + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow13_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_40 z * u12 z = pow13_41_q z * f z + pow13_41 z + (41 : R) * pow13_41_mul_t z := by
  simp only [pow13_40, u12, pow13_41_q, f, pow13_41, pow13_41_mul_t]
  simp only [pow12_41]
  ring

theorem pow13_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_40 z * u12 z = pow13_41_q z * f z + pow13_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_41_mul_integer z


theorem pow13_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_40 z * u12 z = pow13_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_41_mul z


theorem pow13_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 41 = pow13_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow13_40_pow z hz]
  exact pow13_41_root z hz


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_41 z

theorem iterate13 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 13) = u13 z := by
  calc
    _ = (z ^ (41 ^ 12)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate12 z hz)
    _ = _ := pow13_41_pow z hz


def pow14_2 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (39 + z * (30 + z * (23 + z * (27 + z * (17 + z * (29 + z * (28 + z * (14 + z * (4 + z * (15 + z * (25 + z * (32 + z * (18 + z * (38 + z * (8 + z * (26 + z * (40 + z * (40 + z * 21)))))))))))))))))))

def pow14_2_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (14 + z * (32 + z * (33 + z * (39 + z * (14 + z * (13 + z * (25 + z * (3 + z * (11 + z * (22 + z * (35 + z * (14 + z * (23 + z * (24 + z * (29 + z * (28 + z * (20 + z * 16))))))))))))))))))

def pow14_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-10) + z * (9 + z * ((-35) + z * (5 + z * ((-10) + z * (38 + z * (52 + z * (50 + z * (94 + z * (104 + z * (125 + z * (52 + z * (103 + z * (97 + z * (33 + z * (26 + z * (22 + z * ((-10) + z * ((-64) + z * ((-68) + z * ((-28) + z * ((-70) + z * ((-48) + z * ((-69) + z * ((-36) + z * ((-69) + z * ((-83) + z * ((-70) + z * ((-91) + z * ((-88) + z * ((-105) + z * ((-79) + z * ((-79) + z * ((-64) + z * ((-49) + z * ((-35) + z * ((-19) + z * ((-12) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow14_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z + (41 : R) * pow14_2_mul_t z := by
  simp only [u13, pow14_2_q, f, pow14_2, pow14_2_mul_t]
  simp only [pow13_41]
  ring

theorem pow14_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_2_mul_integer z


theorem pow14_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z * u13 z = pow14_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_2_mul z


theorem pow14_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 2 = pow14_2 z := by
  calc
    _ = u13 z ^ 1 * u13 z ^ 1 := by ring
    _ = u13 z * u13 z := by simp only [pow_one]
    _ = _ := pow14_2_root z hz


def pow14_4 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (26 + z * (7 + z * (39 + z * (17 + z * (16 + z * (3 + z * (19 + z * (21 + z * (12 + z * (10 + z * (25 + z * (25 + z * (28 + z * (35 + z * (25 + z * (30 + z * (34 + z * (11 + z * 22)))))))))))))))))))

def pow14_4_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (13 + z * (3 + z * (39 + z * (25 + z * (25 + z * (6 + z * (16 + z * (14 + z * (24 + z * (0 + z * (6 + z * (37 + z * (1 + z * (33 + z * (14 + z * (15 + z * (12 + z * 31))))))))))))))))))

def pow14_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (13 + z * (47 + z * (27 + z * (43 + z * (27 + z * (68 + z * (59 + z * (82 + z * (54 + z * (50 + z * (42 + z * (54 + z * (99 + z * (69 + z * (105 + z * (47 + z * (129 + z * (140 + z * (137 + z * (133 + z * (120 + z * (69 + z * (83 + z * (112 + z * (83 + z * (55 + z * (36 + z * (65 + z * (72 + z * (92 + z * (69 + z * (60 + z * (30 + z * (49 + z * (71 + z * (58 + z * (18 + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow14_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z + (41 : R) * pow14_4_mul_t z := by
  simp only [pow14_2, pow14_4_q, f, pow14_4, pow14_4_mul_t]
  
  ring

theorem pow14_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_4_mul_integer z


theorem pow14_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_2 z * pow14_2 z = pow14_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_4_mul z


theorem pow14_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 4 = pow14_4 z := by
  calc
    _ = u13 z ^ 2 * u13 z ^ 2 := by ring
    _ = pow14_2 z * pow14_2 z := by rw [pow14_2_pow z hz]
    _ = _ := pow14_4_root z hz


def pow14_5 {R : Type*} [CommRing R] (z : R) : R := (4 + z * (0 + z * (23 + z * (16 + z * (0 + z * (26 + z * (39 + z * (16 + z * (8 + z * (5 + z * (28 + z * (36 + z * (37 + z * (12 + z * (24 + z * (28 + z * (17 + z * (15 + z * (35 + z * 23)))))))))))))))))))

def pow14_5_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (28 + z * (16 + z * (23 + z * (29 + z * (3 + z * (28 + z * (35 + z * (8 + z * (19 + z * (39 + z * (8 + z * (33 + z * (40 + z * (17 + z * (15 + z * (23 + z * (9 + z * 6))))))))))))))))))

def pow14_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-8) + z * ((-27) + z * (3 + z * ((-4) + z * (14 + z * (21 + z * (10 + z * (20 + z * (32 + z * (8 + z * (3 + z * (10 + z * (30 + z * ((-38) + z * (9 + z * ((-3) + z * (2 + z * (10 + z * (31 + z * (25 + z * (18 + z * (30 + z * (10 + z * (8 + z * ((-16) + z * ((-20) + z * ((-28) + z * ((-50) + z * ((-41) + z * ((-41) + z * ((-36) + z * ((-40) + z * ((-12) + z * ((-5) + z * ((-9) + z * (2 + z * ((-3) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow14_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_4 z * u13 z = pow14_5_q z * f z + pow14_5 z + (41 : R) * pow14_5_mul_t z := by
  simp only [pow14_4, u13, pow14_5_q, f, pow14_5, pow14_5_mul_t]
  simp only [pow13_41]
  ring

theorem pow14_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_4 z * u13 z = pow14_5_q z * f z + pow14_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_5_mul_integer z


theorem pow14_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_4 z * u13 z = pow14_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_5_mul z


theorem pow14_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 5 = pow14_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow14_4_pow z hz]
  exact pow14_5_root z hz


def pow14_10 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (5 + z * (18 + z * (10 + z * (17 + z * (23 + z * (23 + z * (8 + z * (26 + z * (0 + z * (16 + z * (40 + z * (11 + z * (8 + z * (33 + z * (9 + z * (24 + z * (4 + z * (12 + z * 21)))))))))))))))))))

def pow14_10_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (13 + z * (10 + z * (5 + z * (4 + z * (40 + z * (38 + z * (19 + z * (3 + z * (4 + z * (0 + z * (1 + z * (13 + z * (12 + z * (26 + z * (10 + z * (21 + z * (8 + z * 37))))))))))))))))))

def pow14_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-22) + z * ((-33) + z * ((-15) + z * ((-26) + z * ((-32) + z * ((-46) + z * ((-58) + z * ((-3) + z * ((-25) + z * ((-20) + z * (5 + z * (22 + z * (15 + z * ((-11) + z * ((-8) + z * ((-8) + z * (66 + z * (27 + z * (13 + z * (36 + z * (78 + z * (48 + z * (75 + z * (103 + z * (72 + z * (81 + z * (72 + z * (72 + z * (82 + z * (82 + z * (36 + z * (10 + z * (13 + z * (15 + z * (5 + z * (25 + z * (12 + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow14_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_5 z * pow14_5 z = pow14_10_q z * f z + pow14_10 z + (41 : R) * pow14_10_mul_t z := by
  simp only [pow14_5, pow14_10_q, f, pow14_10, pow14_10_mul_t]
  
  ring

theorem pow14_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_5 z * pow14_5 z = pow14_10_q z * f z + pow14_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_10_mul_integer z


theorem pow14_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_5 z * pow14_5 z = pow14_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_10_mul z


theorem pow14_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 10 = pow14_10 z := by
  calc
    _ = u13 z ^ 5 * u13 z ^ 5 := by ring
    _ = pow14_5 z * pow14_5 z := by rw [pow14_5_pow z hz]
    _ = _ := pow14_10_root z hz


def pow14_20 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (18 + z * (37 + z * (11 + z * (34 + z * (27 + z * (17 + z * (33 + z * (27 + z * (15 + z * (4 + z * (10 + z * (18 + z * (18 + z * (23 + z * (18 + z * (10 + z * (0 + z * (4 + z * 37)))))))))))))))))))

def pow14_20_q {R : Type*} [CommRing R] (z : R) : R := (8 + z * (15 + z * (8 + z * (27 + z * (28 + z * (26 + z * (33 + z * (9 + z * (38 + z * (28 + z * (10 + z * (14 + z * (32 + z * (21 + z * (31 + z * (11 + z * (19 + z * (25 + z * 31))))))))))))))))))

def pow14_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-12) + z * ((-3) + z * ((-25) + z * ((-22) + z * ((-33) + z * ((-25) + z * ((-27) + z * ((-41) + z * ((-41) + z * ((-36) + z * ((-16) + z * ((-55) + z * ((-45) + z * ((-39) + z * ((-61) + z * ((-41) + z * ((-68) + z * ((-75) + z * ((-60) + z * ((-103) + z * ((-65) + z * ((-47) + z * ((-96) + z * ((-60) + z * ((-63) + z * ((-51) + z * ((-44) + z * ((-75) + z * ((-52) + z * ((-7) + z * ((-63) + z * ((-48) + z * ((-42) + z * ((-32) + z * ((-15) + z * ((-24) + z * ((-11) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow14_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_10 z * pow14_10 z = pow14_20_q z * f z + pow14_20 z + (41 : R) * pow14_20_mul_t z := by
  simp only [pow14_10, pow14_20_q, f, pow14_20, pow14_20_mul_t]
  
  ring

theorem pow14_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_10 z * pow14_10 z = pow14_20_q z * f z + pow14_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_20_mul_integer z


theorem pow14_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_10 z * pow14_10 z = pow14_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_20_mul z


theorem pow14_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 20 = pow14_20 z := by
  calc
    _ = u13 z ^ 10 * u13 z ^ 10 := by ring
    _ = pow14_10 z * pow14_10 z := by rw [pow14_10_pow z hz]
    _ = _ := pow14_20_root z hz


def pow14_40 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (8 + z * (29 + z * (20 + z * (28 + z * (9 + z * (1 + z * (15 + z * (20 + z * (19 + z * (6 + z * (39 + z * (40 + z * (16 + z * (37 + z * (28 + z * (24 + z * (3 + z * 19))))))))))))))))))

def pow14_40_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (13 + z * (25 + z * (0 + z * (14 + z * (40 + z * (27 + z * (5 + z * (9 + z * (18 + z * (10 + z * (39 + z * (29 + z * (8 + z * (16 + z * (27 + z * (16 + z * (21 + z * 16))))))))))))))))))

def pow14_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-12) + z * ((-20) + z * (15 + z * (10 + z * (0 + z * (21 + z * (34 + z * (49 + z * (54 + z * (61 + z * (37 + z * (6 + z * ((-5) + z * (34 + z * (15 + z * ((-2) + z * ((-5) + z * ((-18) + z * ((-37) + z * ((-4) + z * (14 + z * ((-41) + z * ((-2) + z * ((-34) + z * ((-57) + z * ((-21) + z * ((-25) + z * ((-46) + z * ((-61) + z * ((-60) + z * ((-41) + z * ((-30) + z * ((-18) + z * ((-17) + z * ((-12) + z * ((-22) + z * ((-5) + z * 33))))))))))))))))))))))))))))))))))))))

theorem pow14_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_20 z * pow14_20 z = pow14_40_q z * f z + pow14_40 z + (41 : R) * pow14_40_mul_t z := by
  simp only [pow14_20, pow14_40_q, f, pow14_40, pow14_40_mul_t]
  
  ring

theorem pow14_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_20 z * pow14_20 z = pow14_40_q z * f z + pow14_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_40_mul_integer z


theorem pow14_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_20 z * pow14_20 z = pow14_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_40_mul z


theorem pow14_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 40 = pow14_40 z := by
  calc
    _ = u13 z ^ 20 * u13 z ^ 20 := by ring
    _ = pow14_20 z * pow14_20 z := by rw [pow14_20_pow z hz]
    _ = _ := pow14_40_root z hz


def pow14_41 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (40 + z * (16 + z * (8 + z * (24 + z * (12 + z * (40 + z * (1 + z * (21 + z * (19 + z * (12 + z * (2 + z * (34 + z * (16 + z * (3 + z * (3 + z * (24 + z * (14 + z * (19 + z * 7)))))))))))))))))))

def pow14_41_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (30 + z * (15 + z * (17 + z * (20 + z * (17 + z * (4 + z * (25 + z * (33 + z * (4 + z * (35 + z * (4 + z * (14 + z * (37 + z * (36 + z * (19 + z * (6 + z * 35)))))))))))))))))

def pow14_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-10) + z * (6 + z * (7 + z * (25 + z * (16 + z * (34 + z * (46 + z * (33 + z * (40 + z * (30 + z * (53 + z * (52 + z * (46 + z * (36 + z * (34 + z * (60 + z * (15 + z * (42 + z * (51 + z * (37 + z * (13 + z * (7 + z * (6 + z * ((-30) + z * ((-47) + z * ((-27) + z * ((-48) + z * ((-44) + z * ((-81) + z * ((-38) + z * ((-52) + z * ((-64) + z * ((-47) + z * ((-26) + z * ((-10) + z * ((-25) + z * 1)))))))))))))))))))))))))))))))))))))

theorem pow14_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_40 z * u13 z = pow14_41_q z * f z + pow14_41 z + (41 : R) * pow14_41_mul_t z := by
  simp only [pow14_40, u13, pow14_41_q, f, pow14_41, pow14_41_mul_t]
  simp only [pow13_41]
  ring

theorem pow14_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_40 z * u13 z = pow14_41_q z * f z + pow14_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_41_mul_integer z


theorem pow14_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_40 z * u13 z = pow14_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_41_mul z


theorem pow14_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 41 = pow14_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow14_40_pow z hz]
  exact pow14_41_root z hz


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_41 z

theorem iterate14 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 14) = u14 z := by
  calc
    _ = (z ^ (41 ^ 13)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate13 z hz)
    _ = _ := pow14_41_pow z hz

end DimensionTen.Mod41

end

end OAI
