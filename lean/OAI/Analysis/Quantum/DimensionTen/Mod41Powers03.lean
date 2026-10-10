import OAI.Analysis.Quantum.DimensionTen.Mod41Powers02

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow5_2 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (29 + z * (19 + z * (32 + z * (31 + z * (11 + z * (22 + z * (7 + z * (1 + z * (40 + z * (5 + z * (23 + z * (37 + z * (39 + z * (6 + z * (35 + z * (39 + z * (20 + z * (13 + z * 28)))))))))))))))))))

def pow5_2_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (38 + z * (39 + z * (10 + z * (19 + z * (27 + z * (29 + z * (4 + z * (14 + z * (13 + z * (28 + z * (38 + z * (23 + z * (3 + z * (35 + z * (7 + z * (15 + z * (23 + z * 33))))))))))))))))))

def pow5_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-40) + z * ((-70) + z * ((-38) + z * ((-57) + z * ((-34) + z * ((-28) + z * ((-17) + z * ((-20) + z * ((-2) + z * (8 + z * (28 + z * ((-5) + z * (6 + z * (19 + z * (24 + z * (14 + z * (32 + z * (14 + z * (59 + z * (76 + z * (105 + z * (145 + z * (165 + z * (143 + z * (85 + z * (79 + z * (68 + z * (72 + z * (74 + z * (65 + z * (63 + z * (70 + z * (48 + z * (56 + z * (49 + z * (39 + z * (15 + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow5_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z + (41 : R) * pow5_2_mul_t z := by
  simp only [u4, pow5_2_q, f, pow5_2, pow5_2_mul_t]
  simp only [pow4_41]
  ring

theorem pow5_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_2_mul_integer z


theorem pow5_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z * u4 z = pow5_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_2_mul z


theorem pow5_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 2 = pow5_2 z := by
  calc
    _ = u4 z ^ 1 * u4 z ^ 1 := by ring
    _ = u4 z * u4 z := by simp only [pow_one]
    _ = _ := pow5_2_root z hz


def pow5_4 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (25 + z * (1 + z * (23 + z * (22 + z * (17 + z * (34 + z * (9 + z * (16 + z * (35 + z * (24 + z * (24 + z * (14 + z * (21 + z * (9 + z * (21 + z * (30 + z * (25 + z * (6 + z * 9)))))))))))))))))))

def pow5_4_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (19 + z * (35 + z * (5 + z * (5 + z * (28 + z * (34 + z * (0 + z * (1 + z * (39 + z * (17 + z * (39 + z * (33 + z * (36 + z * (2 + z * (13 + z * (18 + z * (4 + z * 5))))))))))))))))))

def pow5_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-3) + z * ((-9) + z * (14 + z * (35 + z * (33 + z * (8 + z * (50 + z * (22 + z * ((-17) + z * (21 + z * ((-19) + z * (25 + z * ((-9) + z * (56 + z * (82 + z * (61 + z * (42 + z * (102 + z * (91 + z * (36 + z * (59 + z * (96 + z * (13 + z * (43 + z * (66 + z * (28 + z * (20 + z * (88 + z * (47 + z * (45 + z * (77 + z * (72 + z * (43 + z * (59 + z * (48 + z * (26 + z * (14 + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow5_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z + (41 : R) * pow5_4_mul_t z := by
  simp only [pow5_2, pow5_4_q, f, pow5_4, pow5_4_mul_t]
  
  ring

theorem pow5_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_4_mul_integer z


theorem pow5_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_2 z * pow5_2 z = pow5_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_4_mul z


theorem pow5_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 4 = pow5_4 z := by
  calc
    _ = u4 z ^ 2 * u4 z ^ 2 := by ring
    _ = pow5_2 z * pow5_2 z := by rw [pow5_2_pow z hz]
    _ = _ := pow5_4_root z hz


def pow5_5 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (26 + z * (29 + z * (37 + z * (16 + z * (21 + z * (12 + z * (18 + z * (5 + z * (11 + z * (37 + z * (36 + z * (22 + z * (18 + z * (4 + z * (40 + z * (16 + z * (30 + z * (8 + z * 17)))))))))))))))))))

def pow5_5_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (28 + z * (1 + z * (8 + z * (17 + z * (8 + z * (5 + z * (3 + z * (3 + z * (32 + z * (24 + z * (33 + z * (32 + z * (17 + z * (2 + z * (16 + z * (12 + z * (19 + z * 34))))))))))))))))))

def pow5_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-21) + z * ((-20) + z * ((-12) + z * ((-5) + z * (1 + z * (44 + z * (32 + z * (21 + z * (43 + z * (44 + z * (27 + z * (31 + z * (27 + z * (81 + z * (61 + z * (61 + z * (72 + z * (59 + z * (63 + z * (70 + z * (126 + z * (100 + z * (101 + z * (84 + z * (37 + z * (27 + z * (41 + z * (15 + z * (7 + z * (24 + z * (22 + z * (13 + z * (15 + z * (15 + z * (13 + z * ((-2) + z * ((-14) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow5_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_4 z * u4 z = pow5_5_q z * f z + pow5_5 z + (41 : R) * pow5_5_mul_t z := by
  simp only [pow5_4, u4, pow5_5_q, f, pow5_5, pow5_5_mul_t]
  simp only [pow4_41]
  ring

theorem pow5_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_4 z * u4 z = pow5_5_q z * f z + pow5_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_5_mul_integer z


theorem pow5_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_4 z * u4 z = pow5_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_5_mul z


theorem pow5_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 5 = pow5_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow5_4_pow z hz]
  exact pow5_5_root z hz


def pow5_10 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (39 + z * (12 + z * (34 + z * (7 + z * (23 + z * (1 + z * (25 + z * (27 + z * (20 + z * (3 + z * (7 + z * (26 + z * (31 + z * (20 + z * (0 + z * (23 + z * (5 + z * (13 + z * 26)))))))))))))))))))

def pow5_10_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (30 + z * (34 + z * (33 + z * (27 + z * (9 + z * (17 + z * (0 + z * (28 + z * (7 + z * (37 + z * (26 + z * (33 + z * (25 + z * (1 + z * (13 + z * (20 + z * (7 + z * 2))))))))))))))))))

def pow5_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-20) + z * ((-26) + z * ((-3) + z * ((-5) + z * (17 + z * (21 + z * (18 + z * ((-15) + z * (0 + z * ((-35) + z * ((-2) + z * ((-4) + z * (41 + z * (28 + z * (5 + z * (14 + z * ((-2) + z * (32 + z * ((-16) + z * (31 + z * (35 + z * (56 + z * (1 + z * (5 + z * (19 + z * (31 + z * (5 + z * (29 + z * (6 + z * (33 + z * ((-6) + z * (31 + z * (17 + z * (38 + z * (6 + z * (20 + z * (5 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow5_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_5 z * pow5_5 z = pow5_10_q z * f z + pow5_10 z + (41 : R) * pow5_10_mul_t z := by
  simp only [pow5_5, pow5_10_q, f, pow5_10, pow5_10_mul_t]
  
  ring

theorem pow5_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_5 z * pow5_5 z = pow5_10_q z * f z + pow5_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_10_mul_integer z


theorem pow5_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_5 z * pow5_5 z = pow5_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_10_mul z


theorem pow5_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 10 = pow5_10 z := by
  calc
    _ = u4 z ^ 5 * u4 z ^ 5 := by ring
    _ = pow5_5 z * pow5_5 z := by rw [pow5_5_pow z hz]
    _ = _ := pow5_10_root z hz


def pow5_20 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (1 + z * (28 + z * (37 + z * (29 + z * (8 + z * (21 + z * (8 + z * (15 + z * (35 + z * (9 + z * (6 + z * (35 + z * (25 + z * (34 + z * (32 + z * (27 + z * (13 + z * (9 + z * 13)))))))))))))))))))

def pow5_20_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (30 + z * (27 + z * (23 + z * (17 + z * (8 + z * (28 + z * (28 + z * (39 + z * (31 + z * (6 + z * (18 + z * (24 + z * (29 + z * (21 + z * (32 + z * (23 + z * (35 + z * 20))))))))))))))))))

def pow5_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * (25 + z * (19 + z * (16 + z * (34 + z * (10 + z * (12 + z * ((-2) + z * (18 + z * ((-5) + z * (5 + z * ((-29) + z * ((-1) + z * ((-9) + z * (20 + z * ((-33) + z * ((-36) + z * ((-64) + z * ((-103) + z * ((-44) + z * ((-52) + z * ((-29) + z * ((-78) + z * ((-102) + z * ((-89) + z * ((-84) + z * ((-48) + z * ((-63) + z * ((-73) + z * ((-69) + z * ((-56) + z * ((-55) + z * ((-45) + z * ((-57) + z * ((-54) + z * ((-11) + z * ((-24) + z * (1 + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow5_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_10 z * pow5_10 z = pow5_20_q z * f z + pow5_20 z + (41 : R) * pow5_20_mul_t z := by
  simp only [pow5_10, pow5_20_q, f, pow5_20, pow5_20_mul_t]
  
  ring

theorem pow5_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_10 z * pow5_10 z = pow5_20_q z * f z + pow5_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_20_mul_integer z


theorem pow5_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_10 z * pow5_10 z = pow5_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_20_mul z


theorem pow5_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 20 = pow5_20 z := by
  calc
    _ = u4 z ^ 10 * u4 z ^ 10 := by ring
    _ = pow5_10 z * pow5_10 z := by rw [pow5_10_pow z hz]
    _ = _ := pow5_20_root z hz


def pow5_40 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (4 + z * (21 + z * (27 + z * (36 + z * (31 + z * (32 + z * (22 + z * (1 + z * (40 + z * (32 + z * (14 + z * (14 + z * (17 + z * (8 + z * (39 + z * (30 + z * (19 + z * (34 + z * 15)))))))))))))))))))

def pow5_40_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (4 + z * (2 + z * (26 + z * (15 + z * (38 + z * (36 + z * (36 + z * (40 + z * (7 + z * (3 + z * (38 + z * (28 + z * (9 + z * (12 + z * (29 + z * (28 + z * (2 + z * 5))))))))))))))))))

def pow5_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (22 + z * ((-3) + z * (38 + z * (32 + z * (40 + z * (3 + z * (48 + z * ((-18) + z * ((-6) + z * (32 + z * ((-11) + z * (1 + z * (40 + z * (8 + z * (32 + z * (36 + z * (52 + z * (72 + z * (72 + z * (21 + z * ((-3) + z * (32 + z * ((-44) + z * ((-46) + z * ((-8) + z * (3 + z * ((-13) + z * (4 + z * (59 + z * (38 + z * (6 + z * (15 + z * (13 + z * (10 + z * ((-2) + z * ((-2) + z * (6 + z * (2 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow5_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_20 z * pow5_20 z = pow5_40_q z * f z + pow5_40 z + (41 : R) * pow5_40_mul_t z := by
  simp only [pow5_20, pow5_40_q, f, pow5_40, pow5_40_mul_t]
  
  ring

theorem pow5_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_20 z * pow5_20 z = pow5_40_q z * f z + pow5_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_40_mul_integer z


theorem pow5_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_20 z * pow5_20 z = pow5_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_40_mul z


theorem pow5_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 40 = pow5_40 z := by
  calc
    _ = u4 z ^ 20 * u4 z ^ 20 := by ring
    _ = pow5_20 z * pow5_20 z := by rw [pow5_20_pow z hz]
    _ = _ := pow5_40_root z hz


def pow5_41 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (27 + z * (33 + z * (10 + z * (7 + z * (20 + z * (9 + z * (5 + z * (10 + z * (21 + z * (32 + z * (35 + z * (17 + z * (32 + z * (1 + z * (24 + z * (30 + z * (12 + z * (4 + z * 21)))))))))))))))))))

def pow5_41_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (29 + z * (18 + z * (36 + z * (36 + z * (38 + z * (17 + z * (34 + z * (14 + z * (26 + z * (40 + z * (36 + z * (19 + z * (27 + z * (23 + z * (33 + z * (40 + z * (13 + z * 2))))))))))))))))))

def pow5_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-25) + z * ((-26) + z * ((-39) + z * ((-37) + z * ((-50) + z * ((-10) + z * ((-25) + z * (2 + z * (2 + z * (26 + z * ((-19) + z * ((-15) + z * ((-3) + z * ((-3) + z * (1 + z * ((-12) + z * ((-10) + z * ((-15) + z * (10 + z * (36 + z * (71 + z * (47 + z * (58 + z * (44 + z * (20 + z * (11 + z * (15 + z * (23 + z * (20 + z * (3 + z * (3 + z * (21 + z * (48 + z * (46 + z * (34 + z * (42 + z * (30 + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow5_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_40 z * u4 z = pow5_41_q z * f z + pow5_41 z + (41 : R) * pow5_41_mul_t z := by
  simp only [pow5_40, u4, pow5_41_q, f, pow5_41, pow5_41_mul_t]
  simp only [pow4_41]
  ring

theorem pow5_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_40 z * u4 z = pow5_41_q z * f z + pow5_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_41_mul_integer z


theorem pow5_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_40 z * u4 z = pow5_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_41_mul z


theorem pow5_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 41 = pow5_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow5_40_pow z hz]
  exact pow5_41_root z hz


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_41 z

theorem iterate5 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 5) = u5 z := by
  calc
    _ = (z ^ (41 ^ 4)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u4 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate4 z hz)
    _ = _ := pow5_41_pow z hz


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (29 + z * (33 + z * (21 + z * (21 + z * (30 + z * (33 + z * (2 + z * (0 + z * (10 + z * (14 + z * (38 + z * (36 + z * (33 + z * (38 + z * (34 + z * (17 + z * (32 + z * (35 + z * 2)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (2 + z * (19 + z * (17 + z * (12 + z * (33 + z * (34 + z * (31 + z * (32 + z * (1 + z * (13 + z * (11 + z * (19 + z * (37 + z * (1 + z * (38 + z * (16 + z * (17 + z * 31))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * (18 + z * (14 + z * (31 + z * ((-7) + z * ((-4) + z * ((-16) + z * ((-50) + z * ((-49) + z * ((-31) + z * ((-7) + z * (38 + z * (21 + z * (23 + z * ((-8) + z * ((-38) + z * ((-8) + z * ((-43) + z * ((-17) + z * ((-57) + z * ((-32) + z * (4 + z * ((-66) + z * ((-50) + z * ((-32) + z * ((-31) + z * (3 + z * ((-14) + z * (13 + z * ((-13) + z * ((-21) + z * ((-31) + z * ((-27) + z * ((-44) + z * ((-35) + z * ((-4) + z * ((-13) + z * ((-19) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow6_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z + (41 : R) * pow6_2_mul_t z := by
  simp only [u5, pow6_2_q, f, pow6_2, pow6_2_mul_t]
  simp only [pow5_41]
  ring

theorem pow6_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_2_mul_integer z


theorem pow6_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z * u5 z = pow6_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_2_mul z


theorem pow6_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 2 = pow6_2 z := by
  calc
    _ = u5 z ^ 1 * u5 z ^ 1 := by ring
    _ = u5 z * u5 z := by simp only [pow_one]
    _ = _ := pow6_2_root z hz


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (6 + z * (3 + z * (6 + z * (26 + z * (35 + z * (21 + z * (3 + z * (40 + z * (10 + z * (16 + z * (28 + z * (7 + z * (26 + z * (2 + z * (11 + z * (10 + z * (11 + z * (5 + z * 32)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (28 + z * (28 + z * (7 + z * (26 + z * (13 + z * (16 + z * (10 + z * (28 + z * (23 + z * (3 + z * (16 + z * (35 + z * (16 + z * (25 + z * (31 + z * (22 + z * (29 + z * (20 + z * 4))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (6 + z * (30 + z * (29 + z * (37 + z * (41 + z * (98 + z * (35 + z * (10 + z * (9 + z * (6 + z * (19 + z * (47 + z * (77 + z * (83 + z * (86 + z * (112 + z * (138 + z * (111 + z * (94 + z * (90 + z * (45 + z * (27 + z * (68 + z * (57 + z * (33 + z * (49 + z * (63 + z * (91 + z * (102 + z * (63 + z * (51 + z * (41 + z * (20 + z * (14 + z * (24 + z * (16 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow6_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z + (41 : R) * pow6_4_mul_t z := by
  simp only [pow6_2, pow6_4_q, f, pow6_4, pow6_4_mul_t]
  
  ring

theorem pow6_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_4_mul_integer z


theorem pow6_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_2 z * pow6_2 z = pow6_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_4_mul z


theorem pow6_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 4 = pow6_4 z := by
  calc
    _ = u5 z ^ 2 * u5 z ^ 2 := by ring
    _ = pow6_2 z * pow6_2 z := by rw [pow6_2_pow z hz]
    _ = _ := pow6_4_root z hz


def pow6_5 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (19 + z * (23 + z * (15 + z * (7 + z * (30 + z * (31 + z * (21 + z * (9 + z * (20 + z * (11 + z * (1 + z * (17 + z * (19 + z * (12 + z * (8 + z * (17 + z * (31 + z * (11 + z * 40)))))))))))))))))))

def pow6_5_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (13 + z * (20 + z * (10 + z * (27 + z * (7 + z * (10 + z * (10 + z * (40 + z * (37 + z * (5 + z * (9 + z * (23 + z * (19 + z * (17 + z * (39 + z * (24 + z * (40 + z * 16))))))))))))))))))

def pow6_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-1) + z * ((-15) + z * ((-10) + z * ((-33) + z * (18 + z * (16 + z * (10 + z * ((-26) + z * ((-18) + z * (12 + z * ((-8) + z * ((-26) + z * (8 + z * (0 + z * ((-31) + z * ((-46) + z * ((-59) + z * ((-38) + z * ((-61) + z * ((-29) + z * (19 + z * ((-41) + z * ((-54) + z * ((-37) + z * ((-68) + z * ((-51) + z * ((-55) + z * ((-54) + z * ((-30) + z * ((-33) + z * ((-76) + z * ((-52) + z * ((-72) + z * ((-42) + z * ((-13) + z * ((-21) + z * ((-7) + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow6_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_4 z * u5 z = pow6_5_q z * f z + pow6_5 z + (41 : R) * pow6_5_mul_t z := by
  simp only [pow6_4, u5, pow6_5_q, f, pow6_5, pow6_5_mul_t]
  simp only [pow5_41]
  ring

theorem pow6_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_4 z * u5 z = pow6_5_q z * f z + pow6_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_5_mul_integer z


theorem pow6_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_4 z * u5 z = pow6_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_5_mul z


theorem pow6_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 5 = pow6_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow6_4_pow z hz]
  exact pow6_5_root z hz


def pow6_10 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (33 + z * (7 + z * (33 + z * (11 + z * (34 + z * (8 + z * (18 + z * (23 + z * (39 + z * (27 + z * (5 + z * (29 + z * (22 + z * (9 + z * (24 + z * (14 + z * (15 + z * (32 + z * 29)))))))))))))))))))

def pow6_10_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * (33 + z * (19 + z * (26 + z * (20 + z * (12 + z * (9 + z * (16 + z * (0 + z * (4 + z * (16 + z * (1 + z * (14 + z * (0 + z * (25 + z * (3 + z * (30 + z * 1))))))))))))))))))

def pow6_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-19) + z * ((-36) + z * ((-18) + z * ((-39) + z * ((-31) + z * ((-22) + z * (9 + z * (7 + z * ((-5) + z * (7 + z * (10 + z * ((-1) + z * ((-16) + z * (20 + z * ((-28) + z * ((-21) + z * ((-63) + z * (2 + z * ((-20) + z * (25 + z * (16 + z * (39 + z * (37 + z * (50 + z * (57 + z * (42 + z * (5 + z * (19 + z * (20 + z * (2 + z * (20 + z * (9 + z * (16 + z * (11 + z * (34 + z * (41 + z * (20 + z * 39))))))))))))))))))))))))))))))))))))))

theorem pow6_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_5 z * pow6_5 z = pow6_10_q z * f z + pow6_10 z + (41 : R) * pow6_10_mul_t z := by
  simp only [pow6_5, pow6_10_q, f, pow6_10, pow6_10_mul_t]
  
  ring

theorem pow6_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_5 z * pow6_5 z = pow6_10_q z * f z + pow6_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_10_mul_integer z


theorem pow6_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_5 z * pow6_5 z = pow6_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_10_mul z


theorem pow6_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 10 = pow6_10 z := by
  calc
    _ = u5 z ^ 5 * u5 z ^ 5 := by ring
    _ = pow6_5 z * pow6_5 z := by rw [pow6_5_pow z hz]
    _ = _ := pow6_10_root z hz


def pow6_20 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (17 + z * (9 + z * (12 + z * (33 + z * (1 + z * (35 + z * (28 + z * (34 + z * (27 + z * (2 + z * (9 + z * (21 + z * (19 + z * (23 + z * (23 + z * (17 + z * (22 + z * (24 + z * 2)))))))))))))))))))

def pow6_20_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (26 + z * (30 + z * (16 + z * (30 + z * (7 + z * (1 + z * (17 + z * (4 + z * (24 + z * (31 + z * (4 + z * (0 + z * (25 + z * (34 + z * (27 + z * (17 + z * (37 + z * 21))))))))))))))))))

def pow6_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (31 + z * ((-18) + z * (32 + z * ((-4) + z * (43 + z * (47 + z * (13 + z * (61 + z * (60 + z * (98 + z * (8 + z * (84 + z * (100 + z * (28 + z * (46 + z * (24 + z * ((-2) + z * (56 + z * (72 + z * (51 + z * (28 + z * (75 + z * (54 + z * (36 + z * (5 + z * (20 + z * (64 + z * (27 + z * ((-30) + z * ((-4) + z * (6 + z * ((-39) + z * ((-34) + z * ((-4) + z * (3 + z * (10 + z * (29 + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow6_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_10 z * pow6_10 z = pow6_20_q z * f z + pow6_20 z + (41 : R) * pow6_20_mul_t z := by
  simp only [pow6_10, pow6_20_q, f, pow6_20, pow6_20_mul_t]
  
  ring

theorem pow6_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_10 z * pow6_10 z = pow6_20_q z * f z + pow6_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_20_mul_integer z


theorem pow6_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_10 z * pow6_10 z = pow6_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_20_mul z


theorem pow6_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 20 = pow6_20 z := by
  calc
    _ = u5 z ^ 10 * u5 z ^ 10 := by ring
    _ = pow6_10 z * pow6_10 z := by rw [pow6_10_pow z hz]
    _ = _ := pow6_20_root z hz


def pow6_40 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (32 + z * (4 + z * (29 + z * (16 + z * (36 + z * (33 + z * (13 + z * (13 + z * (22 + z * (24 + z * (31 + z * (27 + z * (24 + z * (16 + z * (4 + z * (29 + z * (37 + z * (39 + z * 37)))))))))))))))))))

def pow6_40_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (40 + z * (5 + z * (20 + z * (0 + z * (27 + z * (37 + z * (38 + z * (23 + z * (20 + z * (1 + z * (9 + z * (29 + z * (7 + z * (28 + z * (8 + z * (4 + z * (17 + z * 4))))))))))))))))))

def pow6_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-12) + z * ((-11) + z * ((-20) + z * (43 + z * ((-39) + z * (32 + z * ((-1) + z * (22 + z * (7 + z * (18 + z * ((-6) + z * (28 + z * (37 + z * (8 + z * (50 + z * ((-9) + z * (10 + z * (33 + z * ((-6) + z * (16 + z * (29 + z * (13 + z * (6 + z * (13 + z * (4 + z * (15 + z * (8 + z * ((-18) + z * (9 + z * (19 + z * (7 + z * (18 + z * (4 + z * (13 + z * (15 + z * (2 + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow6_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_20 z * pow6_20 z = pow6_40_q z * f z + pow6_40 z + (41 : R) * pow6_40_mul_t z := by
  simp only [pow6_20, pow6_40_q, f, pow6_40, pow6_40_mul_t]
  
  ring

theorem pow6_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_20 z * pow6_20 z = pow6_40_q z * f z + pow6_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_40_mul_integer z


theorem pow6_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_20 z * pow6_20 z = pow6_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_40_mul z


theorem pow6_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 40 = pow6_40 z := by
  calc
    _ = u5 z ^ 20 * u5 z ^ 20 := by ring
    _ = pow6_20 z * pow6_20 z := by rw [pow6_20_pow z hz]
    _ = _ := pow6_40_root z hz


def pow6_41 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (37 + z * (38 + z * (22 + z * (29 + z * (11 + z * (22 + z * (17 + z * (6 + z * (17 + z * (3 + z * (35 + z * (14 + z * (6 + z * (30 + z * (1 + z * (28 + z * (6 + z * (2 + z * 36)))))))))))))))))))

def pow6_41_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (28 + z * (0 + z * (31 + z * (18 + z * (12 + z * (31 + z * (39 + z * (9 + z * (9 + z * (19 + z * (23 + z * (36 + z * (5 + z * (0 + z * (29 + z * (39 + z * (2 + z * 39))))))))))))))))))

def pow6_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-15) + z * ((-8) + z * ((-3) + z * ((-15) + z * ((-2) + z * (30 + z * ((-31) + z * ((-27) + z * ((-5) + z * ((-5) + z * ((-14) + z * (6 + z * (35 + z * (12 + z * ((-19) + z * (1 + z * (7 + z * ((-5) + z * (20 + z * (16 + z * (70 + z * ((-6) + z * ((-13) + z * (37 + z * ((-6) + z * ((-17) + z * (26 + z * (58 + z * (48 + z * (19 + z * ((-7) + z * (10 + z * ((-2) + z * ((-4) + z * (5 + z * (15 + z * ((-5) + z * 18))))))))))))))))))))))))))))))))))))))

theorem pow6_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_40 z * u5 z = pow6_41_q z * f z + pow6_41 z + (41 : R) * pow6_41_mul_t z := by
  simp only [pow6_40, u5, pow6_41_q, f, pow6_41, pow6_41_mul_t]
  simp only [pow5_41]
  ring

theorem pow6_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_40 z * u5 z = pow6_41_q z * f z + pow6_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_41_mul_integer z


theorem pow6_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_40 z * u5 z = pow6_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_41_mul z


theorem pow6_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 41 = pow6_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow6_40_pow z hz]
  exact pow6_41_root z hz


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_41 z

theorem iterate6 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 6) = u6 z := by
  calc
    _ = (z ^ (41 ^ 5)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate5 z hz)
    _ = _ := pow6_41_pow z hz

end DimensionTen.Mod41

end

end OAI
