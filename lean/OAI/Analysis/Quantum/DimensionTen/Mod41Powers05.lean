import OAI.Analysis.Quantum.DimensionTen.Mod41Powers04

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow9_2 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (11 + z * (14 + z * (3 + z * (7 + z * (33 + z * (2 + z * (37 + z * (0 + z * (38 + z * (40 + z * (16 + z * (21 + z * (28 + z * (8 + z * (29 + z * (16 + z * (37 + z * (27 + z * 9)))))))))))))))))))

def pow9_2_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (1 + z * (6 + z * (5 + z * (7 + z * (19 + z * (39 + z * (3 + z * (25 + z * (36 + z * (14 + z * (6 + z * (13 + z * (1 + z * (34 + z * (26 + z * (31 + z * (40 + z * 1))))))))))))))))))

def pow9_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (0 + z * (8 + z * (30 + z * (3 + z * (41 + z * (0 + z * (39 + z * (16 + z * (35 + z * (16 + z * (30 + z * (72 + z * (21 + z * (81 + z * (59 + z * (15 + z * (56 + z * (101 + z * (64 + z * (112 + z * (57 + z * (69 + z * (54 + z * (31 + z * (16 + z * (40 + z * (44 + z * (12 + z * (66 + z * (55 + z * (4 + z * (26 + z * (10 + z * (0 + z * (15 + z * (1 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow9_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z + (41 : R) * pow9_2_mul_t z := by
  simp only [u8, pow9_2_q, f, pow9_2, pow9_2_mul_t]
  simp only [pow8_41]
  ring

theorem pow9_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_2_mul_integer z


theorem pow9_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z * u8 z = pow9_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_2_mul z


theorem pow9_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 2 = pow9_2 z := by
  calc
    _ = u8 z ^ 1 * u8 z ^ 1 := by ring
    _ = u8 z * u8 z := by simp only [pow_one]
    _ = _ := pow9_2_root z hz


def pow9_4 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (10 + z * (23 + z * (32 + z * (32 + z * (26 + z * (5 + z * (15 + z * (10 + z * (37 + z * (25 + z * (29 + z * (34 + z * (35 + z * (28 + z * (39 + z * (0 + z * (21 + z * (40 + z * 37)))))))))))))))))))

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (36 + z * (16 + z * (5 + z * (2 + z * (5 + z * (29 + z * (33 + z * (30 + z * (5 + z * (19 + z * (31 + z * (26 + z * (8 + z * (36 + z * (1 + z * (36 + z * (24 + z * 40))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * ((-35) + z * ((-32) + z * ((-29) + z * ((-21) + z * ((-29) + z * ((-23) + z * ((-31) + z * ((-70) + z * ((-36) + z * ((-33) + z * ((-35) + z * ((-16) + z * ((-54) + z * (3 + z * ((-33) + z * ((-47) + z * ((-9) + z * ((-74) + z * (18 + z * (28 + z * ((-26) + z * (49 + z * (8 + z * (40 + z * ((-9) + z * (14 + z * (34 + z * (31 + z * ((-15) + z * (4 + z * ((-14) + z * ((-15) + z * ((-31) + z * (5 + z * ((-3) + z * ((-1) + z * ((-18) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow9_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z + (41 : R) * pow9_4_mul_t z := by
  simp only [pow9_2, pow9_4_q, f, pow9_4, pow9_4_mul_t]
  
  ring

theorem pow9_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_4_mul_integer z


theorem pow9_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_2 z * pow9_2 z = pow9_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_4_mul z


theorem pow9_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 4 = pow9_4 z := by
  calc
    _ = u8 z ^ 2 * u8 z ^ 2 := by ring
    _ = pow9_2 z * pow9_2 z := by rw [pow9_2_pow z hz]
    _ = _ := pow9_4_root z hz


def pow9_5 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (27 + z * (1 + z * (19 + z * (20 + z * (9 + z * (16 + z * (11 + z * (21 + z * (15 + z * (32 + z * (11 + z * (38 + z * (25 + z * (28 + z * (40 + z * (25 + z * (32 + z * (6 + z * 29)))))))))))))))))))

def pow9_5_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (7 + z * (27 + z * (35 + z * (25 + z * (24 + z * (36 + z * (22 + z * (1 + z * (8 + z * (6 + z * (17 + z * (15 + z * (8 + z * (25 + z * (23 + z * (20 + z * 37))))))))))))))))))

def pow9_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-8) + z * ((-9) + z * ((-4) + z * ((-18) + z * ((-4) + z * ((-3) + z * ((-25) + z * ((-22) + z * (23 + z * (27 + z * (16 + z * (34 + z * (42 + z * (43 + z * (33 + z * (65 + z * (63 + z * (58 + z * (54 + z * (92 + z * (102 + z * (50 + z * (32 + z * (92 + z * (74 + z * (97 + z * (101 + z * (88 + z * (73 + z * (87 + z * (45 + z * (30 + z * (28 + z * (1 + z * (18 + z * (33 + z * (5 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow9_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_4 z * u8 z = pow9_5_q z * f z + pow9_5 z + (41 : R) * pow9_5_mul_t z := by
  simp only [pow9_4, u8, pow9_5_q, f, pow9_5, pow9_5_mul_t]
  simp only [pow8_41]
  ring

theorem pow9_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_4 z * u8 z = pow9_5_q z * f z + pow9_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_5_mul_integer z


theorem pow9_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_4 z * u8 z = pow9_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_5_mul z


theorem pow9_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 5 = pow9_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow9_4_pow z hz]
  exact pow9_5_root z hz


def pow9_10 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (20 + z * (17 + z * (33 + z * (24 + z * (16 + z * (35 + z * (20 + z * (27 + z * (12 + z * (34 + z * (13 + z * (4 + z * (33 + z * (31 + z * (8 + z * (25 + z * (3 + z * (25 + z * 19)))))))))))))))))))

def pow9_10_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (33 + z * (11 + z * (30 + z * (12 + z * (35 + z * (4 + z * (25 + z * (40 + z * (25 + z * (3 + z * (24 + z * (7 + z * (2 + z * (0 + z * (19 + z * (32 + z * (5 + z * 21))))))))))))))))))

def pow9_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-8) + z * ((-25) + z * ((-32) + z * ((-6) + z * ((-49) + z * (2 + z * ((-48) + z * ((-45) + z * ((-47) + z * ((-13) + z * ((-33) + z * ((-27) + z * (35 + z * (34 + z * (2 + z * (4 + z * (25 + z * (12 + z * (0 + z * (36 + z * (53 + z * (41 + z * (41 + z * (51 + z * (90 + z * (58 + z * (99 + z * (95 + z * (140 + z * (73 + z * (97 + z * (66 + z * (42 + z * (42 + z * (7 + z * (33 + z * ((-7) + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow9_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_5 z * pow9_5 z = pow9_10_q z * f z + pow9_10 z + (41 : R) * pow9_10_mul_t z := by
  simp only [pow9_5, pow9_10_q, f, pow9_10, pow9_10_mul_t]
  
  ring

theorem pow9_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_5 z * pow9_5 z = pow9_10_q z * f z + pow9_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_10_mul_integer z


theorem pow9_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_5 z * pow9_5 z = pow9_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_10_mul z


theorem pow9_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 10 = pow9_10 z := by
  calc
    _ = u8 z ^ 5 * u8 z ^ 5 := by ring
    _ = pow9_5 z * pow9_5 z := by rw [pow9_5_pow z hz]
    _ = _ := pow9_10_root z hz


def pow9_20 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (17 + z * (29 + z * (39 + z * (19 + z * (7 + z * (1 + z * (21 + z * (40 + z * (33 + z * (11 + z * (28 + z * (4 + z * (14 + z * (11 + z * (38 + z * (17 + z * (1 + z * (31 + z * 12)))))))))))))))))))

def pow9_20_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (18 + z * (0 + z * (37 + z * (24 + z * (12 + z * (13 + z * (26 + z * (26 + z * (7 + z * (9 + z * (23 + z * (37 + z * (30 + z * (14 + z * (25 + z * (25 + z * (1 + z * 33))))))))))))))))))

def pow9_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * (12 + z * (13 + z * (32 + z * (27 + z * (18 + z * (92 + z * (33 + z * (45 + z * (76 + z * (90 + z * (43 + z * (19 + z * (89 + z * (73 + z * ((-12) + z * (69 + z * (44 + z * (19 + z * (35 + z * (16 + z * (61 + z * ((-6) + z * ((-10) + z * (44 + z * ((-18) + z * ((-6) + z * ((-24) + z * ((-17) + z * ((-18) + z * ((-48) + z * ((-38) + z * (1 + z * ((-23) + z * ((-18) + z * ((-11) + z * (3 + z * ((-1) + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow9_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_10 z * pow9_10 z = pow9_20_q z * f z + pow9_20 z + (41 : R) * pow9_20_mul_t z := by
  simp only [pow9_10, pow9_20_q, f, pow9_20, pow9_20_mul_t]
  
  ring

theorem pow9_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_10 z * pow9_10 z = pow9_20_q z * f z + pow9_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_20_mul_integer z


theorem pow9_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_10 z * pow9_10 z = pow9_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_20_mul z


theorem pow9_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 20 = pow9_20 z := by
  calc
    _ = u8 z ^ 10 * u8 z ^ 10 := by ring
    _ = pow9_10 z * pow9_10 z := by rw [pow9_10_pow z hz]
    _ = _ := pow9_20_root z hz


def pow9_40 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (9 + z * (19 + z * (6 + z * (14 + z * (7 + z * (3 + z * (30 + z * (25 + z * (35 + z * (3 + z * (40 + z * (40 + z * (0 + z * (36 + z * (15 + z * (32 + z * (2 + z * (31 + z * 19)))))))))))))))))))

def pow9_40_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (39 + z * (27 + z * (1 + z * (28 + z * (6 + z * (18 + z * (12 + z * (7 + z * (37 + z * (0 + z * (20 + z * (30 + z * (36 + z * (22 + z * (14 + z * (37 + z * (32 + z * 21))))))))))))))))))

def pow9_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * ((-10) + z * (9 + z * (54 + z * (27 + z * (35 + z * (7 + z * (43 + z * (25 + z * (31 + z * (82 + z * (86 + z * (47 + z * ((-14) + z * (8 + z * (29 + z * ((-12) + z * ((-11) + z * (51 + z * (18 + z * ((-53) + z * ((-15) + z * (26 + z * ((-16) + z * ((-28) + z * ((-46) + z * (17 + z * ((-27) + z * ((-85) + z * ((-35) + z * ((-45) + z * ((-61) + z * ((-81) + z * ((-23) + z * ((-13) + z * ((-41) + z * ((-9) + z * (2 + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow9_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_20 z * pow9_20 z = pow9_40_q z * f z + pow9_40 z + (41 : R) * pow9_40_mul_t z := by
  simp only [pow9_20, pow9_40_q, f, pow9_40, pow9_40_mul_t]
  
  ring

theorem pow9_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_20 z * pow9_20 z = pow9_40_q z * f z + pow9_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_40_mul_integer z


theorem pow9_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_20 z * pow9_20 z = pow9_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_40_mul z


theorem pow9_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 40 = pow9_40 z := by
  calc
    _ = u8 z ^ 20 * u8 z ^ 20 := by ring
    _ = pow9_20 z * pow9_20 z := by rw [pow9_20_pow z hz]
    _ = _ := pow9_40_root z hz


def pow9_41 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (6 + z * (36 + z * (24 + z * (2 + z * (8 + z * (20 + z * (7 + z * (9 + z * (9 + z * (30 + z * (24 + z * (12 + z * (29 + z * (12 + z * (26 + z * (24 + z * (16 + z * (26 + z * 1)))))))))))))))))))

def pow9_41_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (36 + z * (6 + z * (6 + z * (30 + z * (12 + z * (20 + z * (28 + z * (31 + z * (34 + z * (4 + z * (31 + z * (11 + z * (19 + z * (33 + z * (25 + z * (11 + z * (3 + z * 19))))))))))))))))))

def pow9_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (12 + z * ((-23) + z * (10 + z * ((-3) + z * ((-6) + z * ((-9) + z * ((-18) + z * (26 + z * ((-53) + z * ((-4) + z * (1 + z * ((-12) + z * (14 + z * ((-14) + z * (70 + z * ((-23) + z * (13 + z * (33 + z * (23 + z * (38 + z * ((-6) + z * (65 + z * ((-12) + z * (34 + z * (29 + z * (28 + z * (46 + z * (40 + z * (16 + z * (46 + z * (20 + z * (25 + z * (21 + z * (22 + z * (20 + z * (14 + z * (31 + z * (3 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow9_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_40 z * u8 z = pow9_41_q z * f z + pow9_41 z + (41 : R) * pow9_41_mul_t z := by
  simp only [pow9_40, u8, pow9_41_q, f, pow9_41, pow9_41_mul_t]
  simp only [pow8_41]
  ring

theorem pow9_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_40 z * u8 z = pow9_41_q z * f z + pow9_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_41_mul_integer z


theorem pow9_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_40 z * u8 z = pow9_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_41_mul z


theorem pow9_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 41 = pow9_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow9_40_pow z hz]
  exact pow9_41_root z hz


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_41 z

theorem iterate9 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 9) = u9 z := by
  calc
    _ = (z ^ (41 ^ 8)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u8 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate8 z hz)
    _ = _ := pow9_41_pow z hz


def pow10_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (32 + z * (11 + z * (32 + z * (36 + z * (37 + z * (7 + z * (11 + z * (14 + z * (13 + z * (10 + z * (25 + z * (20 + z * (18 + z * (28 + z * (3 + z * (7 + z * (24 + z * (28 + z * 19)))))))))))))))))))

def pow10_2_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (15 + z * (14 + z * (16 + z * (17 + z * (32 + z * (8 + z * (38 + z * (27 + z * (29 + z * (0 + z * (33 + z * (26 + z * (38 + z * (1 + z * (4 + z * (31 + z * (22 + z * 1))))))))))))))))))

def pow10_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-12) + z * (14 + z * (8 + z * ((-3) + z * ((-8) + z * (0 + z * ((-57) + z * ((-21) + z * ((-63) + z * ((-5) + z * ((-54) + z * ((-23) + z * ((-18) + z * ((-28) + z * ((-32) + z * ((-36) + z * ((-34) + z * ((-14) + z * ((-49) + z * ((-52) + z * ((-31) + z * ((-59) + z * ((-68) + z * ((-65) + z * ((-24) + z * ((-16) + z * ((-43) + z * ((-12) + z * (14 + z * ((-14) + z * ((-3) + z * ((-25) + z * (13 + z * (9 + z * ((-11) + z * (0 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow10_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z + (41 : R) * pow10_2_mul_t z := by
  simp only [u9, pow10_2_q, f, pow10_2, pow10_2_mul_t]
  simp only [pow9_41]
  ring

theorem pow10_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_2_mul_integer z


theorem pow10_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z * u9 z = pow10_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_2_mul z


theorem pow10_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 2 = pow10_2 z := by
  calc
    _ = u9 z ^ 1 * u9 z ^ 1 := by ring
    _ = u9 z * u9 z := by simp only [pow_one]
    _ = _ := pow10_2_root z hz


def pow10_4 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (9 + z * (0 + z * (30 + z * (19 + z * (11 + z * (37 + z * (27 + z * (32 + z * (2 + z * (25 + z * (7 + z * (26 + z * (39 + z * (15 + z * (10 + z * (0 + z * (30 + z * (12 + z * 32)))))))))))))))))))

def pow10_4_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (7 + z * (14 + z * (26 + z * (31 + z * (23 + z * (27 + z * (5 + z * (14 + z * (6 + z * (10 + z * (32 + z * (15 + z * (40 + z * (38 + z * (40 + z * (22 + z * (33 + z * 33))))))))))))))))))

def pow10_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-7) + z * (9 + z * ((-16) + z * (5 + z * (18 + z * (35 + z * (32 + z * (41 + z * (52 + z * (14 + z * ((-13) + z * (15 + z * ((-23) + z * ((-2) + z * ((-15) + z * ((-5) + z * ((-39) + z * ((-45) + z * ((-33) + z * ((-46) + z * ((-30) + z * ((-24) + z * ((-10) + z * ((-49) + z * ((-76) + z * ((-55) + z * ((-61) + z * ((-65) + z * ((-82) + z * ((-67) + z * ((-50) + z * ((-75) + z * ((-75) + z * ((-58) + z * ((-10) + z * (3 + z * (1 + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow10_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z + (41 : R) * pow10_4_mul_t z := by
  simp only [pow10_2, pow10_4_q, f, pow10_4, pow10_4_mul_t]
  
  ring

theorem pow10_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_4_mul_integer z


theorem pow10_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_2 z * pow10_2 z = pow10_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_4_mul z


theorem pow10_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 4 = pow10_4 z := by
  calc
    _ = u9 z ^ 2 * u9 z ^ 2 := by ring
    _ = pow10_2 z * pow10_2 z := by rw [pow10_2_pow z hz]
    _ = _ := pow10_4_root z hz


def pow10_5 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (39 + z * (35 + z * (10 + z * (11 + z * (33 + z * (28 + z * (30 + z * (7 + z * (18 + z * (5 + z * (19 + z * (14 + z * (39 + z * (5 + z * (28 + z * (27 + z * (31 + z * (25 + z * 17)))))))))))))))))))

def pow10_5_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (20 + z * (10 + z * (32 + z * (28 + z * (7 + z * (20 + z * (38 + z * (28 + z * (22 + z * (39 + z * (32 + z * (37 + z * (36 + z * (28 + z * (17 + z * (18 + z * (7 + z * 32))))))))))))))))))

def pow10_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-14) + z * ((-11) + z * ((-15) + z * ((-27) + z * ((-18) + z * (12 + z * ((-29) + z * ((-25) + z * ((-12) + z * ((-32) + z * ((-79) + z * ((-63) + z * ((-33) + z * ((-71) + z * ((-63) + z * ((-38) + z * ((-60) + z * ((-99) + z * ((-35) + z * ((-76) + z * ((-30) + z * ((-88) + z * ((-51) + z * ((-49) + z * ((-78) + z * ((-86) + z * ((-79) + z * ((-52) + z * ((-67) + z * ((-30) + z * ((-34) + z * ((-29) + z * ((-31) + z * ((-11) + z * (8 + z * (2 + z * ((-3) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow10_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_4 z * u9 z = pow10_5_q z * f z + pow10_5 z + (41 : R) * pow10_5_mul_t z := by
  simp only [pow10_4, u9, pow10_5_q, f, pow10_5, pow10_5_mul_t]
  simp only [pow9_41]
  ring

theorem pow10_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_4 z * u9 z = pow10_5_q z * f z + pow10_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_5_mul_integer z


theorem pow10_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_4 z * u9 z = pow10_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_5_mul z


theorem pow10_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 5 = pow10_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow10_4_pow z hz]
  exact pow10_5_root z hz


def pow10_10 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (21 + z * (15 + z * (28 + z * (26 + z * (26 + z * (23 + z * (32 + z * (12 + z * (12 + z * (16 + z * (9 + z * (4 + z * (27 + z * (8 + z * (39 + z * (40 + z * (3 + z * (17 + z * 13)))))))))))))))))))

def pow10_10_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (6 + z * (9 + z * (5 + z * (39 + z * (16 + z * (7 + z * (17 + z * (39 + z * (0 + z * (12 + z * (17 + z * (36 + z * (40 + z * (2 + z * (13 + z * (3 + z * (11 + z * 2))))))))))))))))))

def pow10_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (44 + z * (64 + z * (68 + z * (8 + z * (47 + z * (75 + z * (108 + z * (44 + z * (64 + z * (45 + z * (46 + z * (19 + z * (76 + z * (72 + z * (19 + z * (74 + z * (103 + z * (163 + z * (80 + z * (94 + z * (55 + z * (69 + z * (21 + z * (59 + z * (43 + z * (36 + z * ((-28) + z * (29 + z * (23 + z * (50 + z * (39 + z * (47 + z * (59 + z * (61 + z * (52 + z * (32 + z * (19 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow10_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_5 z * pow10_5 z = pow10_10_q z * f z + pow10_10 z + (41 : R) * pow10_10_mul_t z := by
  simp only [pow10_5, pow10_10_q, f, pow10_10, pow10_10_mul_t]
  
  ring

theorem pow10_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_5 z * pow10_5 z = pow10_10_q z * f z + pow10_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_10_mul_integer z


theorem pow10_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_5 z * pow10_5 z = pow10_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_10_mul z


theorem pow10_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 10 = pow10_10 z := by
  calc
    _ = u9 z ^ 5 * u9 z ^ 5 := by ring
    _ = pow10_5 z * pow10_5 z := by rw [pow10_5_pow z hz]
    _ = _ := pow10_10_root z hz


def pow10_20 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (14 + z * (35 + z * (11 + z * (4 + z * (29 + z * (39 + z * (37 + z * (36 + z * (19 + z * (21 + z * (6 + z * (21 + z * (38 + z * (1 + z * (32 + z * (32 + z * (4 + z * (37 + z * 36)))))))))))))))))))

def pow10_20_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (3 + z * (25 + z * (15 + z * (11 + z * (4 + z * (36 + z * (9 + z * (30 + z * (34 + z * (0 + z * (29 + z * (20 + z * (23 + z * (35 + z * (16 + z * (9 + z * (5 + z * 5))))))))))))))))))

def pow10_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * (14 + z * ((-13) + z * (24 + z * (13 + z * (53 + z * (29 + z * (58 + z * (34 + z * (34 + z * (33 + z * (17 + z * (25 + z * ((-12) + z * (3 + z * ((-4) + z * (23 + z * (19 + z * (22 + z * (45 + z * (52 + z * (20 + z * (25 + z * (11 + z * ((-27) + z * ((-39) + z * ((-12) + z * ((-57) + z * ((-28) + z * ((-4) + z * ((-27) + z * (33 + z * (13 + z * ((-3) + z * (35 + z * (16 + z * (3 + z * (7 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow10_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_10 z * pow10_10 z = pow10_20_q z * f z + pow10_20 z + (41 : R) * pow10_20_mul_t z := by
  simp only [pow10_10, pow10_20_q, f, pow10_20, pow10_20_mul_t]
  
  ring

theorem pow10_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_10 z * pow10_10 z = pow10_20_q z * f z + pow10_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_20_mul_integer z


theorem pow10_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_10 z * pow10_10 z = pow10_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_20_mul z


theorem pow10_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 20 = pow10_20 z := by
  calc
    _ = u9 z ^ 10 * u9 z ^ 10 := by ring
    _ = pow10_10 z * pow10_10 z := by rw [pow10_10_pow z hz]
    _ = _ := pow10_20_root z hz


def pow10_40 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (33 + z * (13 + z * (13 + z * (40 + z * (25 + z * (19 + z * (35 + z * (1 + z * (15 + z * (0 + z * (28 + z * (5 + z * (22 + z * (22 + z * (37 + z * (25 + z * (16 + z * (4 + z * 16)))))))))))))))))))

def pow10_40_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (19 + z * (16 + z * (22 + z * (1 + z * (24 + z * (10 + z * (30 + z * (30 + z * (37 + z * (6 + z * (38 + z * (14 + z * (1 + z * (18 + z * (39 + z * (23 + z * (28 + z * 25))))))))))))))))))

def pow10_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (11 + z * (0 + z * (30 + z * (6 + z * (0 + z * (21 + z * (72 + z * (58 + z * (100 + z * (37 + z * (71 + z * (5 + z * (74 + z * (116 + z * (82 + z * (98 + z * (33 + z * (22 + z * (93 + z * (53 + z * (98 + z * (133 + z * (21 + z * (66 + z * (75 + z * (78 + z * (46 + z * (10 + z * (45 + z * (11 + z * ((-28) + z * (61 + z * (11 + z * ((-21) + z * (40 + z * (20 + z * (9 + z * (46 + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow10_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_20 z * pow10_20 z = pow10_40_q z * f z + pow10_40 z + (41 : R) * pow10_40_mul_t z := by
  simp only [pow10_20, pow10_40_q, f, pow10_40, pow10_40_mul_t]
  
  ring

theorem pow10_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_20 z * pow10_20 z = pow10_40_q z * f z + pow10_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_40_mul_integer z


theorem pow10_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_20 z * pow10_20 z = pow10_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_40_mul z


theorem pow10_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 40 = pow10_40 z := by
  calc
    _ = u9 z ^ 20 * u9 z ^ 20 := by ring
    _ = pow10_20 z * pow10_20 z := by rw [pow10_20_pow z hz]
    _ = _ := pow10_40_root z hz


def pow10_41 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (1 + z * (13 + z * (12 + z * (15 + z * (31 + z * (3 + z * (30 + z * (19 + z * (21 + z * (6 + z * (8 + z * (4 + z * (23 + z * (19 + z * (4 + z * (0 + z * (11 + z * (10 + z * 5)))))))))))))))))))

def pow10_41_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (22 + z * (30 + z * (36 + z * (8 + z * (20 + z * (7 + z * (18 + z * (8 + z * (9 + z * (16 + z * (7 + z * (40 + z * (19 + z * (15 + z * (17 + z * (18 + z * (22 + z * 16))))))))))))))))))

def pow10_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (1 + z * ((-1) + z * (0 + z * (7 + z * ((-19) + z * (35 + z * (18 + z * (7 + z * (3 + z * (0 + z * (21 + z * ((-33) + z * (17 + z * ((-8) + z * (39 + z * (7 + z * (24 + z * (4 + z * ((-12) + z * ((-23) + z * ((-10) + z * (4 + z * ((-14) + z * ((-10) + z * (5 + z * ((-11) + z * ((-13) + z * ((-23) + z * ((-5) + z * ((-2) + z * ((-19) + z * ((-8) + z * ((-10) + z * ((-10) + z * ((-10) + z * ((-14) + z * ((-2) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow10_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_40 z * u9 z = pow10_41_q z * f z + pow10_41 z + (41 : R) * pow10_41_mul_t z := by
  simp only [pow10_40, u9, pow10_41_q, f, pow10_41, pow10_41_mul_t]
  simp only [pow9_41]
  ring

theorem pow10_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_40 z * u9 z = pow10_41_q z * f z + pow10_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_41_mul_integer z


theorem pow10_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_40 z * u9 z = pow10_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_41_mul z


theorem pow10_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 41 = pow10_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow10_40_pow z hz]
  exact pow10_41_root z hz


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_41 z

theorem iterate10 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 10) = u10 z := by
  calc
    _ = (z ^ (41 ^ 9)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u9 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate9 z hz)
    _ = _ := pow10_41_pow z hz

end DimensionTen.Mod41

end

end OAI
