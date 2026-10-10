import OAI.Analysis.Quantum.DimensionTen.Mod41Powers03

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (9 + z * (18 + z * (33 + z * (3 + z * (19 + z * (30 + z * (10 + z * (1 + z * (12 + z * (31 + z * (13 + z * (37 + z * (15 + z * (37 + z * (15 + z * (24 + z * (27 + z * (39 + z * (32 + z * 38)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (19 + z * (30 + z * (36 + z * (14 + z * (9 + z * (33 + z * (30 + z * (31 + z * (12 + z * (1 + z * (29 + z * (11 + z * (32 + z * (9 + z * (21 + z * (28 + z * (9 + z * 25))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * (29 + z * (35 + z * (46 + z * (48 + z * (51 + z * (49 + z * (16 + z * (5 + z * (12 + z * ((-17) + z * (1 + z * (29 + z * ((-2) + z * (9 + z * ((-31) + z * ((-11) + z * ((-43) + z * ((-55) + z * ((-48) + z * ((-8) + z * ((-21) + z * ((-68) + z * ((-29) + z * ((-82) + z * ((-21) + z * ((-62) + z * ((-51) + z * ((-16) + z * ((-70) + z * (9 + z * ((-43) + z * ((-52) + z * (0 + z * ((-47) + z * (11 + z * ((-7) + z * ((-15) + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow7_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z + (41 : R) * pow7_2_mul_t z := by
  simp only [u6, pow7_2_q, f, pow7_2, pow7_2_mul_t]
  simp only [pow6_41]
  ring

theorem pow7_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_2_mul_integer z


theorem pow7_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z * u6 z = pow7_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_2_mul z


theorem pow7_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 2 = pow7_2 z := by
  calc
    _ = u6 z ^ 1 * u6 z ^ 1 := by ring
    _ = u6 z * u6 z := by simp only [pow_one]
    _ = _ := pow7_2_root z hz


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (26 + z * (13 + z * (34 + z * (5 + z * (36 + z * (19 + z * (32 + z * (7 + z * (7 + z * (18 + z * (29 + z * (24 + z * (35 + z * (3 + z * (34 + z * (18 + z * (39 + z * (18 + z * 12)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (14 + z * (12 + z * (1 + z * (18 + z * (29 + z * (24 + z * (25 + z * (36 + z * (22 + z * (24 + z * (37 + z * (12 + z * (9 + z * (15 + z * (36 + z * (24 + z * (30 + z * 9))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-12) + z * ((-9) + z * (14 + z * ((-5) + z * ((-12) + z * (6 + z * ((-12) + z * ((-59) + z * ((-42) + z * ((-13) + z * ((-26) + z * ((-48) + z * (19 + z * (17 + z * ((-24) + z * ((-33) + z * ((-11) + z * (23 + z * (15 + z * (62 + z * (50 + z * (32 + z * (14 + z * (30 + z * ((-15) + z * (24 + z * (47 + z * (102 + z * (73 + z * (92 + z * (54 + z * (71 + z * (45 + z * (63 + z * (75 + z * (71 + z * (52 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow7_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z + (41 : R) * pow7_4_mul_t z := by
  simp only [pow7_2, pow7_4_q, f, pow7_4, pow7_4_mul_t]
  
  ring

theorem pow7_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_4_mul_integer z


theorem pow7_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_2 z * pow7_2 z = pow7_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_4_mul z


theorem pow7_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 4 = pow7_4 z := by
  calc
    _ = u6 z ^ 2 * u6 z ^ 2 := by ring
    _ = pow7_2 z * pow7_2 z := by rw [pow7_2_pow z hz]
    _ = _ := pow7_4_root z hz


def pow7_5 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (30 + z * (3 + z * (37 + z * (35 + z * (28 + z * (36 + z * (17 + z * (37 + z * (21 + z * (33 + z * (23 + z * (40 + z * (30 + z * (33 + z * (13 + z * (12 + z * (14 + z * 30))))))))))))))))))

def pow7_5_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (33 + z * (16 + z * (1 + z * (32 + z * (8 + z * (0 + z * (19 + z * (18 + z * (38 + z * (16 + z * (28 + z * (14 + z * (12 + z * (19 + z * (39 + z * (40 + z * (12 + z * 22))))))))))))))))))

def pow7_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (14 + z * (33 + z * (45 + z * (37 + z * (51 + z * (57 + z * (102 + z * (30 + z * (24 + z * (38 + z * (16 + z * (46 + z * (45 + z * (87 + z * (9 + z * (7 + z * (58 + z * ((-2) + z * (63 + z * ((-22) + z * (43 + z * (8 + z * ((-48) + z * (3 + z * ((-56) + z * ((-35) + z * ((-43) + z * ((-40) + z * ((-8) + z * ((-47) + z * ((-22) + z * ((-31) + z * ((-39) + z * ((-21) + z * ((-19) + z * (18 + z * (0 + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow7_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_4 z * u6 z = pow7_5_q z * f z + pow7_5 z + (41 : R) * pow7_5_mul_t z := by
  simp only [pow7_4, u6, pow7_5_q, f, pow7_5, pow7_5_mul_t]
  simp only [pow6_41]
  ring

theorem pow7_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_4 z * u6 z = pow7_5_q z * f z + pow7_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_5_mul_integer z


theorem pow7_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_4 z * u6 z = pow7_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_5_mul z


theorem pow7_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 5 = pow7_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow7_4_pow z hz]
  exact pow7_5_root z hz


def pow7_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (24 + z * (28 + z * (2 + z * (32 + z * (11 + z * (33 + z * (17 + z * (11 + z * (2 + z * (30 + z * (22 + z * (25 + z * (37 + z * (28 + z * (3 + z * (39 + z * (1 + z * (26 + z * 8)))))))))))))))))))

def pow7_10_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (28 + z * (27 + z * (12 + z * (24 + z * (23 + z * (31 + z * (9 + z * (39 + z * (12 + z * (11 + z * (1 + z * (10 + z * (6 + z * (26 + z * (39 + z * 39))))))))))))))))

def pow7_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * (1 + z * ((-22) + z * (4 + z * (31 + z * (25 + z * (40 + z * (74 + z * (37 + z * (100 + z * (75 + z * (138 + z * (116 + z * (165 + z * (168 + z * (128 + z * (98 + z * (130 + z * (168 + z * (122 + z * (102 + z * (135 + z * (124 + z * (63 + z * (94 + z * (62 + z * (89 + z * (40 + z * (69 + z * (27 + z * (15 + z * ((-16) + z * ((-8) + z * ((-30) + z * ((-23) + z * ((-9) + z * 21))))))))))))))))))))))))))))))))))))

theorem pow7_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_5 z * pow7_5 z = pow7_10_q z * f z + pow7_10 z + (41 : R) * pow7_10_mul_t z := by
  simp only [pow7_5, pow7_10_q, f, pow7_10, pow7_10_mul_t]
  
  ring

theorem pow7_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_5 z * pow7_5 z = pow7_10_q z * f z + pow7_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_10_mul_integer z


theorem pow7_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_5 z * pow7_5 z = pow7_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_10_mul z


theorem pow7_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 10 = pow7_10 z := by
  calc
    _ = u6 z ^ 5 * u6 z ^ 5 := by ring
    _ = pow7_5 z * pow7_5 z := by rw [pow7_5_pow z hz]
    _ = _ := pow7_10_root z hz


def pow7_20 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (32 + z * (8 + z * (34 + z * (27 + z * (11 + z * (5 + z * (13 + z * (10 + z * (39 + z * (20 + z * (26 + z * (31 + z * (31 + z * (20 + z * (33 + z * (37 + z * (8 + z * (35 + z * 36)))))))))))))))))))

def pow7_20_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (3 + z * (37 + z * (15 + z * (10 + z * (4 + z * (24 + z * (6 + z * (40 + z * (11 + z * (9 + z * (30 + z * (4 + z * (8 + z * (10 + z * (13 + z * (34 + z * (13 + z * 23))))))))))))))))))

def pow7_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-2) + z * ((-23) + z * (5 + z * ((-23) + z * (20 + z * (5 + z * (17 + z * (19 + z * ((-11) + z * ((-16) + z * (5 + z * (40 + z * (2 + z * (80 + z * (27 + z * (25 + z * (47 + z * (24 + z * (6 + z * (80 + z * ((-5) + z * (40 + z * (19 + z * (53 + z * ((-9) + z * (43 + z * ((-10) + z * (34 + z * (43 + z * (17 + z * ((-1) + z * (17 + z * ((-46) + z * (1 + z * ((-27) + z * ((-3) + z * ((-7) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow7_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_10 z * pow7_10 z = pow7_20_q z * f z + pow7_20 z + (41 : R) * pow7_20_mul_t z := by
  simp only [pow7_10, pow7_20_q, f, pow7_20, pow7_20_mul_t]
  
  ring

theorem pow7_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_10 z * pow7_10 z = pow7_20_q z * f z + pow7_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_20_mul_integer z


theorem pow7_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_10 z * pow7_10 z = pow7_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_20_mul z


theorem pow7_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 20 = pow7_20 z := by
  calc
    _ = u6 z ^ 10 * u6 z ^ 10 := by ring
    _ = pow7_10 z * pow7_10 z := by rw [pow7_10_pow z hz]
    _ = _ := pow7_20_root z hz


def pow7_40 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (39 + z * (21 + z * (34 + z * (21 + z * (3 + z * (2 + z * (30 + z * (12 + z * (29 + z * (0 + z * (20 + z * (34 + z * (29 + z * (9 + z * (18 + z * (12 + z * (29 + z * (17 + z * 29)))))))))))))))))))

def pow7_40_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (5 + z * (2 + z * (34 + z * (12 + z * (22 + z * (23 + z * (5 + z * (22 + z * (33 + z * (15 + z * (6 + z * (13 + z * (37 + z * (3 + z * (22 + z * (18 + z * (7 + z * 25))))))))))))))))))

def pow7_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * (14 + z * (24 + z * ((-1) + z * (46 + z * (10 + z * (20 + z * (7 + z * (7 + z * (3 + z * (17 + z * (26 + z * (71 + z * (52 + z * (75 + z * (60 + z * (102 + z * (54 + z * (85 + z * (133 + z * (70 + z * (98 + z * (107 + z * (83 + z * (56 + z * (81 + z * (85 + z * (111 + z * (125 + z * (88 + z * (100 + z * (106 + z * (58 + z * (56 + z * (75 + z * (48 + z * (28 + z * (43 + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow7_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_20 z * pow7_20 z = pow7_40_q z * f z + pow7_40 z + (41 : R) * pow7_40_mul_t z := by
  simp only [pow7_20, pow7_40_q, f, pow7_40, pow7_40_mul_t]
  
  ring

theorem pow7_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_20 z * pow7_20 z = pow7_40_q z * f z + pow7_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_40_mul_integer z


theorem pow7_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_20 z * pow7_20 z = pow7_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_40_mul z


theorem pow7_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 40 = pow7_40 z := by
  calc
    _ = u6 z ^ 20 * u6 z ^ 20 := by ring
    _ = pow7_20 z * pow7_20 z := by rw [pow7_20_pow z hz]
    _ = _ := pow7_40_root z hz


def pow7_41 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (28 + z * (6 + z * (7 + z * (30 + z * (2 + z * (32 + z * (18 + z * (16 + z * (25 + z * (39 + z * (7 + z * (0 + z * (39 + z * (6 + z * (27 + z * (28 + z * (15 + z * (9 + z * 3)))))))))))))))))))

def pow7_41_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (40 + z * (27 + z * (3 + z * (18 + z * (36 + z * (19 + z * (18 + z * (2 + z * (17 + z * (17 + z * (8 + z * (24 + z * (11 + z * (26 + z * (20 + z * (20 + z * (18 + z * 19))))))))))))))))))

def pow7_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * (0 + z * (6 + z * (50 + z * (34 + z * (21 + z * (9 + z * (12 + z * (6 + z * ((-1) + z * (19 + z * (6 + z * (5 + z * (40 + z * (21 + z * (20 + z * ((-56) + z * ((-20) + z * ((-2) + z * (7 + z * (11 + z * ((-9) + z * ((-7) + z * (22 + z * ((-35) + z * ((-26) + z * (0 + z * ((-12) + z * (4 + z * ((-30) + z * ((-9) + z * ((-6) + z * ((-20) + z * ((-18) + z * ((-16) + z * (1 + z * (9 + z * (2 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow7_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_40 z * u6 z = pow7_41_q z * f z + pow7_41 z + (41 : R) * pow7_41_mul_t z := by
  simp only [pow7_40, u6, pow7_41_q, f, pow7_41, pow7_41_mul_t]
  simp only [pow6_41]
  ring

theorem pow7_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_40 z * u6 z = pow7_41_q z * f z + pow7_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_41_mul_integer z


theorem pow7_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_40 z * u6 z = pow7_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_41_mul z


theorem pow7_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 41 = pow7_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow7_40_pow z hz]
  exact pow7_41_root z hz


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_41 z

theorem iterate7 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 7) = u7 z := by
  calc
    _ = (z ^ (41 ^ 6)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate6 z hz)
    _ = _ := pow7_41_pow z hz


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (32 + z * (30 + z * (4 + z * (27 + z * (25 + z * (10 + z * (33 + z * (5 + z * (30 + z * (5 + z * (39 + z * (14 + z * (10 + z * (40 + z * (30 + z * (40 + z * (38 + z * (2 + z * 20)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (33 + z * (20 + z * (40 + z * (0 + z * (36 + z * (11 + z * (23 + z * (14 + z * (40 + z * (37 + z * (3 + z * (31 + z * (13 + z * (22 + z * (23 + z * (20 + z * (30 + z * 9))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (1 + z * ((-13) + z * ((-49) + z * (8 + z * ((-44) + z * (11 + z * ((-20) + z * (9 + z * ((-50) + z * (16 + z * ((-9) + z * ((-68) + z * (3 + z * ((-11) + z * ((-14) + z * ((-27) + z * ((-35) + z * ((-78) + z * ((-24) + z * ((-54) + z * ((-69) + z * ((-28) + z * (8 + z * ((-75) + z * ((-43) + z * ((-16) + z * ((-63) + z * ((-55) + z * ((-41) + z * ((-26) + z * ((-38) + z * ((-33) + z * ((-36) + z * ((-28) + z * ((-22) + z * ((-22) + z * ((-6) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z + (41 : R) * pow8_2_mul_t z := by
  simp only [u7, pow8_2_q, f, pow8_2, pow8_2_mul_t]
  simp only [pow7_41]
  ring

theorem pow8_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_2_mul_integer z


theorem pow8_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z * u7 z = pow8_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_2_mul z


theorem pow8_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 2 = pow8_2 z := by
  calc
    _ = u7 z ^ 1 * u7 z ^ 1 := by ring
    _ = u7 z * u7 z := by simp only [pow_one]
    _ = _ := pow8_2_root z hz


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (29 + z * (10 + z * (10 + z * (23 + z * (26 + z * (7 + z * (22 + z * (37 + z * (17 + z * (29 + z * (15 + z * (15 + z * (6 + z * (19 + z * (3 + z * (15 + z * (23 + z * (1 + z * 36)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (28 + z * (27 + z * (27 + z * (40 + z * (18 + z * (32 + z * (2 + z * (11 + z * (38 + z * (1 + z * (22 + z * (15 + z * (10 + z * (30 + z * (31 + z * (30 + z * (11 + z * (11 + z * 31))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-13) + z * ((-9) + z * ((-15) + z * ((-26) + z * ((-25) + z * (34 + z * ((-14) + z * ((-3) + z * (18 + z * ((-25) + z * (29 + z * ((-14) + z * (30 + z * ((-8) + z * ((-15) + z * (74 + z * (8 + z * (69 + z * ((-4) + z * (37 + z * (76 + z * (0 + z * (72 + z * (35 + z * (34 + z * (63 + z * (17 + z * (82 + z * ((-14) + z * (55 + z * (64 + z * (19 + z * (38 + z * (10 + z * (12 + z * (16 + z * ((-21) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow8_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z + (41 : R) * pow8_4_mul_t z := by
  simp only [pow8_2, pow8_4_q, f, pow8_4, pow8_4_mul_t]
  
  ring

theorem pow8_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_4_mul_integer z


theorem pow8_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_2 z * pow8_2 z = pow8_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_4_mul z


theorem pow8_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 4 = pow8_4 z := by
  calc
    _ = u7 z ^ 2 * u7 z ^ 2 := by ring
    _ = pow8_2 z * pow8_2 z := by rw [pow8_2_pow z hz]
    _ = _ := pow8_4_root z hz


def pow8_5 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (8 + z * (15 + z * (37 + z * (15 + z * (31 + z * (10 + z * (32 + z * (19 + z * (36 + z * (32 + z * (33 + z * (34 + z * (36 + z * (27 + z * (15 + z * (12 + z * (37 + z * (17 + z * 3)))))))))))))))))))

def pow8_5_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (37 + z * (23 + z * (0 + z * (25 + z * (8 + z * (35 + z * (35 + z * (40 + z * (35 + z * (26 + z * (24 + z * (7 + z * (12 + z * (37 + z * (27 + z * (31 + z * (39 + z * 26))))))))))))))))))

def pow8_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-11) + z * ((-30) + z * ((-15) + z * ((-25) + z * (8 + z * ((-22) + z * ((-16) + z * ((-50) + z * ((-29) + z * ((-18) + z * ((-30) + z * ((-37) + z * ((-28) + z * ((-7) + z * ((-77) + z * ((-92) + z * ((-75) + z * ((-86) + z * ((-97) + z * ((-44) + z * ((-74) + z * ((-98) + z * ((-49) + z * ((-97) + z * ((-101) + z * ((-80) + z * ((-57) + z * ((-84) + z * ((-54) + z * ((-64) + z * ((-83) + z * ((-49) + z * ((-81) + z * ((-40) + z * ((-23) + z * ((-25) + z * ((-12) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow8_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_4 z * u7 z = pow8_5_q z * f z + pow8_5 z + (41 : R) * pow8_5_mul_t z := by
  simp only [pow8_4, u7, pow8_5_q, f, pow8_5, pow8_5_mul_t]
  simp only [pow7_41]
  ring

theorem pow8_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_4 z * u7 z = pow8_5_q z * f z + pow8_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_5_mul_integer z


theorem pow8_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_4 z * u7 z = pow8_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_5_mul z


theorem pow8_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 5 = pow8_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow8_4_pow z hz]
  exact pow8_5_root z hz


def pow8_10 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (15 + z * (33 + z * (17 + z * (18 + z * (6 + z * (27 + z * (36 + z * (15 + z * (36 + z * (15 + z * (4 + z * (24 + z * (39 + z * (22 + z * (7 + z * (27 + z * (19 + z * (16 + z * 6)))))))))))))))))))

def pow8_10_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (20 + z * (6 + z * (17 + z * (12 + z * (15 + z * (35 + z * (35 + z * (38 + z * (13 + z * (12 + z * (2 + z * (34 + z * (17 + z * (23 + z * (12 + z * (27 + z * (37 + z * 9))))))))))))))))))

def pow8_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-14) + z * ((-5) + z * (8 + z * (4 + z * (15 + z * (13 + z * (6 + z * ((-5) + z * (23 + z * (47 + z * (59 + z * (79 + z * (97 + z * (94 + z * (97 + z * (85 + z * (97 + z * (100 + z * (88 + z * (130 + z * (100 + z * (105 + z * (62 + z * (62 + z * (60 + z * (79 + z * (55 + z * (40 + z * (40 + z * (39 + z * ((-10) + z * ((-31) + z * ((-37) + z * ((-3) + z * ((-8) + z * ((-19) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_5 z * pow8_5 z = pow8_10_q z * f z + pow8_10 z + (41 : R) * pow8_10_mul_t z := by
  simp only [pow8_5, pow8_10_q, f, pow8_10, pow8_10_mul_t]
  
  ring

theorem pow8_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_5 z * pow8_5 z = pow8_10_q z * f z + pow8_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_10_mul_integer z


theorem pow8_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_5 z * pow8_5 z = pow8_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_10_mul z


theorem pow8_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 10 = pow8_10 z := by
  calc
    _ = u7 z ^ 5 * u7 z ^ 5 := by ring
    _ = pow8_5 z * pow8_5 z := by rw [pow8_5_pow z hz]
    _ = _ := pow8_10_root z hz


def pow8_20 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (29 + z * (1 + z * (12 + z * (12 + z * (3 + z * (38 + z * (20 + z * (21 + z * (20 + z * (31 + z * (22 + z * (27 + z * (13 + z * (16 + z * (23 + z * (6 + z * (13 + z * (36 + z * 1)))))))))))))))))))

def pow8_20_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (3 + z * (38 + z * (11 + z * (25 + z * (30 + z * (38 + z * (9 + z * (21 + z * (37 + z * (31 + z * (23 + z * (16 + z * (21 + z * (4 + z * (29 + z * (26 + z * (14 + z * 36))))))))))))))))))

def pow8_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-11) + z * ((-47) + z * (4 + z * ((-39) + z * ((-8) + z * ((-45) + z * ((-32) + z * ((-6) + z * ((-9) + z * ((-22) + z * ((-14) + z * ((-27) + z * ((-34) + z * (12 + z * (10 + z * ((-6) + z * ((-66) + z * ((-32) + z * ((-15) + z * ((-25) + z * ((-22) + z * ((-14) + z * ((-15) + z * ((-45) + z * ((-29) + z * ((-10) + z * ((-37) + z * ((-42) + z * ((-28) + z * ((-9) + z * ((-17) + z * ((-36) + z * ((-36) + z * ((-37) + z * ((-23) + z * ((-14) + z * ((-22) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_10 z * pow8_10 z = pow8_20_q z * f z + pow8_20 z + (41 : R) * pow8_20_mul_t z := by
  simp only [pow8_10, pow8_20_q, f, pow8_20, pow8_20_mul_t]
  
  ring

theorem pow8_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_10 z * pow8_10 z = pow8_20_q z * f z + pow8_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_20_mul_integer z


theorem pow8_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_10 z * pow8_10 z = pow8_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_20_mul z


theorem pow8_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 20 = pow8_20 z := by
  calc
    _ = u7 z ^ 10 * u7 z ^ 10 := by ring
    _ = pow8_10 z * pow8_10 z := by rw [pow8_10_pow z hz]
    _ = _ := pow8_20_root z hz


def pow8_40 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (16 + z * (24 + z * (21 + z * (19 + z * (1 + z * (34 + z * (28 + z * (40 + z * (21 + z * (18 + z * (3 + z * (40 + z * (21 + z * (10 + z * (2 + z * (5 + z * (12 + z * (10 + z * 38)))))))))))))))))))

def pow8_40_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (16 + z * (25 + z * (29 + z * (26 + z * (20 + z * (18 + z * (29 + z * (26 + z * (6 + z * (2 + z * (31 + z * (28 + z * (8 + z * (7 + z * (9 + z * (4 + z * (1 + z * 1))))))))))))))))))

def pow8_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * (14 + z * ((-9) + z * ((-32) + z * ((-25) + z * ((-40) + z * ((-17) + z * (5 + z * ((-29) + z * ((-9) + z * (13 + z * ((-12) + z * (2 + z * (8 + z * (3 + z * (2 + z * (23 + z * (14 + z * (41 + z * (10 + z * ((-8) + z * (28 + z * ((-10) + z * ((-9) + z * (69 + z * (41 + z * (15 + z * (17 + z * (37 + z * (29 + z * (19 + z * (1 + z * (25 + z * (32 + z * (6 + z * (19 + z * (31 + z * (1 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_20 z * pow8_20 z = pow8_40_q z * f z + pow8_40 z + (41 : R) * pow8_40_mul_t z := by
  simp only [pow8_20, pow8_40_q, f, pow8_40, pow8_40_mul_t]
  
  ring

theorem pow8_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_20 z * pow8_20 z = pow8_40_q z * f z + pow8_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_40_mul_integer z


theorem pow8_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_20 z * pow8_20 z = pow8_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_40_mul z


theorem pow8_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 40 = pow8_40 z := by
  calc
    _ = u7 z ^ 20 * u7 z ^ 20 := by ring
    _ = pow8_20 z * pow8_20 z := by rw [pow8_20_pow z hz]
    _ = _ := pow8_40_root z hz


def pow8_41 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (26 + z * (28 + z * (4 + z * (30 + z * (16 + z * (39 + z * (9 + z * (24 + z * (8 + z * (22 + z * (31 + z * (17 + z * (27 + z * (40 + z * (17 + z * (32 + z * (35 + z * 1)))))))))))))))))))

def pow8_41_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (20 + z * (36 + z * (5 + z * (7 + z * (27 + z * (5 + z * (36 + z * (12 + z * (34 + z * (12 + z * (12 + z * (22 + z * (24 + z * (25 + z * (38 + z * (39 + z * (27 + z * 32))))))))))))))))))

def pow8_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-9) + z * ((-30) + z * (2 + z * ((-15) + z * ((-17) + z * (5 + z * ((-6) + z * (32 + z * ((-37) + z * (39 + z * ((-19) + z * (26 + z * (18 + z * (0 + z * ((-36) + z * ((-45) + z * ((-52) + z * ((-51) + z * ((-19) + z * ((-51) + z * ((-34) + z * ((-23) + z * ((-19) + z * ((-82) + z * ((-32) + z * ((-71) + z * ((-51) + z * ((-57) + z * ((-51) + z * ((-81) + z * ((-100) + z * ((-71) + z * ((-83) + z * ((-48) + z * ((-26) + z * ((-17) + z * ((-15) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow8_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_40 z * u7 z = pow8_41_q z * f z + pow8_41 z + (41 : R) * pow8_41_mul_t z := by
  simp only [pow8_40, u7, pow8_41_q, f, pow8_41, pow8_41_mul_t]
  simp only [pow7_41]
  ring

theorem pow8_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_40 z * u7 z = pow8_41_q z * f z + pow8_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_41_mul_integer z


theorem pow8_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_40 z * u7 z = pow8_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_41_mul z


theorem pow8_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 41 = pow8_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow8_40_pow z hz]
  exact pow8_41_root z hz


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_41 z

theorem iterate8 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 8) = u8 z := by
  calc
    _ = (z ^ (41 ^ 7)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u7 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate7 z hz)
    _ = _ := pow8_41_pow z hz

end DimensionTen.Mod41

end

end OAI
