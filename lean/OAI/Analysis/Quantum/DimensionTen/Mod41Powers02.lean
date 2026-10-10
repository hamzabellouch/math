import OAI.Analysis.Quantum.DimensionTen.Mod41Powers01

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow3_2 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (38 + z * (8 + z * (30 + z * (6 + z * (18 + z * (2 + z * (5 + z * (28 + z * (0 + z * (23 + z * (12 + z * (18 + z * (16 + z * (30 + z * (4 + z * (1 + z * (6 + z * (13 + z * 22)))))))))))))))))))

def pow3_2_q {R : Type*} [CommRing R] (z : R) : R := (13 + z * (38 + z * (24 + z * (39 + z * (39 + z * (8 + z * (37 + z * (39 + z * (19 + z * (14 + z * (18 + z * (36 + z * (19 + z * (23 + z * (15 + z * (5 + z * (30 + z * (30 + z * 21))))))))))))))))))

def pow3_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-37) + z * ((-21) + z * ((-31) + z * ((-12) + z * (12 + z * ((-3) + z * (18 + z * ((-2) + z * (29 + z * (52 + z * (0 + z * (23 + z * (31 + z * (8 + z * (15 + z * (44 + z * (12 + z * (5 + z * (81 + z * (76 + z * (80 + z * (83 + z * (59 + z * (62 + z * (70 + z * (49 + z * (42 + z * (49 + z * (32 + z * (36 + z * (58 + z * (37 + z * (40 + z * (61 + z * (48 + z * (35 + z * (32 + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow3_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z + (41 : R) * pow3_2_mul_t z := by
  simp only [u2, pow3_2_q, f, pow3_2, pow3_2_mul_t]
  simp only [pow2_41]
  ring

theorem pow3_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_2_mul_integer z


theorem pow3_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z * u2 z = pow3_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_2_mul z


theorem pow3_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 2 = pow3_2 z := by
  calc
    _ = u2 z ^ 1 * u2 z ^ 1 := by ring
    _ = u2 z * u2 z := by simp only [pow_one]
    _ = _ := pow3_2_root z hz


def pow3_4 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (4 + z * (24 + z * (10 + z * (10 + z * (28 + z * (34 + z * (11 + z * (3 + z * (0 + z * (25 + z * (22 + z * (4 + z * (38 + z * (6 + z * (17 + z * (33 + z * (32 + z * (15 + z * 35)))))))))))))))))))

def pow3_4_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (17 + z * (6 + z * (18 + z * (25 + z * (29 + z * (20 + z * (15 + z * (31 + z * (39 + z * (11 + z * (18 + z * (10 + z * (40 + z * (14 + z * (30 + z * (30 + z * (33 + z * 33))))))))))))))))))

def pow3_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * (31 + z * (33 + z * (21 + z * (31 + z * ((-16) + z * (7 + z * ((-32) + z * ((-12) + z * ((-33) + z * ((-33) + z * (0 + z * ((-40) + z * ((-25) + z * ((-4) + z * ((-39) + z * ((-88) + z * ((-114) + z * ((-97) + z * ((-89) + z * ((-121) + z * ((-101) + z * ((-81) + z * ((-130) + z * ((-122) + z * ((-129) + z * ((-88) + z * ((-85) + z * ((-104) + z * ((-82) + z * ((-82) + z * ((-70) + z * ((-88) + z * ((-61) + z * ((-74) + z * ((-50) + z * ((-28) + z * ((-11) + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow3_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z + (41 : R) * pow3_4_mul_t z := by
  simp only [pow3_2, pow3_4_q, f, pow3_4, pow3_4_mul_t]
  
  ring

theorem pow3_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_4_mul_integer z


theorem pow3_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_2 z * pow3_2 z = pow3_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_4_mul z


theorem pow3_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 4 = pow3_4 z := by
  calc
    _ = u2 z ^ 2 * u2 z ^ 2 := by ring
    _ = pow3_2 z * pow3_2 z := by rw [pow3_2_pow z hz]
    _ = _ := pow3_4_root z hz


def pow3_5 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (3 + z * (23 + z * (32 + z * (2 + z * (19 + z * (2 + z * (32 + z * (4 + z * (37 + z * (35 + z * (7 + z * (1 + z * (23 + z * (32 + z * (11 + z * (31 + z * (19 + z * (17 + z * 3)))))))))))))))))))

def pow3_5_q {R : Type*} [CommRing R] (z : R) : R := (13 + z * (4 + z * (25 + z * (39 + z * (38 + z * (17 + z * (11 + z * (4 + z * (38 + z * (29 + z * (21 + z * (30 + z * (1 + z * (37 + z * (28 + z * (5 + z * (30 + z * (39 + z * 31))))))))))))))))))

def pow3_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * (3 + z * ((-20) + z * ((-15) + z * ((-35) + z * ((-22) + z * (5 + z * (12 + z * (4 + z * (14 + z * ((-34) + z * ((-31) + z * (2 + z * ((-37) + z * (15 + z * ((-29) + z * ((-19) + z * ((-20) + z * ((-52) + z * (12 + z * (14 + z * (6 + z * (30 + z * (43 + z * ((-17) + z * ((-2) + z * (13 + z * ((-30) + z * ((-12) + z * (13 + z * (2 + z * (26 + z * ((-1) + z * ((-7) + z * (31 + z * (34 + z * (16 + z * (16 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow3_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_4 z * u2 z = pow3_5_q z * f z + pow3_5 z + (41 : R) * pow3_5_mul_t z := by
  simp only [pow3_4, u2, pow3_5_q, f, pow3_5, pow3_5_mul_t]
  simp only [pow2_41]
  ring

theorem pow3_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_4 z * u2 z = pow3_5_q z * f z + pow3_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_5_mul_integer z


theorem pow3_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_4 z * u2 z = pow3_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_5_mul z


theorem pow3_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 5 = pow3_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow3_4_pow z hz]
  exact pow3_5_root z hz


def pow3_10 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (18 + z * (12 + z * (7 + z * (13 + z * (23 + z * (10 + z * (35 + z * (16 + z * (32 + z * (29 + z * (8 + z * (6 + z * (29 + z * (26 + z * (12 + z * (6 + z * (2 + z * (21 + z * 32)))))))))))))))))))

def pow3_10_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (28 + z * (12 + z * (18 + z * (19 + z * (20 + z * (40 + z * (28 + z * (9 + z * (30 + z * (30 + z * (14 + z * (0 + z * (34 + z * (24 + z * (7 + z * (1 + z * (37 + z * 9))))))))))))))))))

def pow3_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-32) + z * ((-5) + z * (23 + z * ((-42) + z * (8 + z * ((-36) + z * ((-16) + z * ((-62) + z * (8 + z * (15 + z * ((-68) + z * (22 + z * ((-29) + z * ((-22) + z * ((-72) + z * (37 + z * ((-55) + z * ((-26) + z * ((-3) + z * ((-32) + z * ((-71) + z * ((-64) + z * (37 + z * ((-46) + z * ((-46) + z * (1 + z * (19 + z * ((-40) + z * ((-37) + z * (9 + z * (7 + z * ((-14) + z * ((-17) + z * (2 + z * ((-1) + z * ((-21) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow3_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_5 z * pow3_5 z = pow3_10_q z * f z + pow3_10 z + (41 : R) * pow3_10_mul_t z := by
  simp only [pow3_5, pow3_10_q, f, pow3_10, pow3_10_mul_t]
  
  ring

theorem pow3_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_5 z * pow3_5 z = pow3_10_q z * f z + pow3_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_10_mul_integer z


theorem pow3_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_5 z * pow3_5 z = pow3_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_10_mul z


theorem pow3_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 10 = pow3_10 z := by
  calc
    _ = u2 z ^ 5 * u2 z ^ 5 := by ring
    _ = pow3_5 z * pow3_5 z := by rw [pow3_5_pow z hz]
    _ = _ := pow3_10_root z hz


def pow3_20 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (13 + z * (8 + z * (35 + z * (3 + z * (0 + z * (35 + z * (4 + z * (32 + z * (19 + z * (18 + z * (34 + z * (11 + z * (2 + z * (7 + z * (38 + z * (22 + z * (24 + z * (15 + z * 39)))))))))))))))))))

def pow3_20_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (12 + z * (9 + z * (2 + z * (34 + z * (29 + z * (23 + z * (26 + z * (8 + z * (23 + z * (32 + z * (3 + z * (0 + z * (14 + z * (19 + z * (38 + z * (21 + z * 40))))))))))))))))))

def pow3_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * (22 + z * (3 + z * (6 + z * (5 + z * (15 + z * ((-1) + z * (15 + z * (8 + z * (36 + z * (33 + z * (6 + z * ((-3) + z * (38 + z * (72 + z * (14 + z * ((-16) + z * ((-23) + z * ((-31) + z * (36 + z * ((-6) + z * ((-24) + z * ((-52) + z * (4 + z * ((-23) + z * ((-65) + z * ((-24) + z * ((-17) + z * (24 + z * ((-22) + z * ((-61) + z * ((-34) + z * ((-16) + z * ((-38) + z * ((-49) + z * ((-48) + z * ((-19) + z * (3 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow3_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_10 z * pow3_10 z = pow3_20_q z * f z + pow3_20 z + (41 : R) * pow3_20_mul_t z := by
  simp only [pow3_10, pow3_20_q, f, pow3_20, pow3_20_mul_t]
  
  ring

theorem pow3_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_10 z * pow3_10 z = pow3_20_q z * f z + pow3_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_20_mul_integer z


theorem pow3_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_10 z * pow3_10 z = pow3_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_20_mul z


theorem pow3_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 20 = pow3_20 z := by
  calc
    _ = u2 z ^ 10 * u2 z ^ 10 := by ring
    _ = pow3_10 z * pow3_10 z := by rw [pow3_10_pow z hz]
    _ = _ := pow3_20_root z hz


def pow3_40 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (20 + z * (9 + z * (9 + z * (34 + z * (36 + z * (15 + z * (22 + z * (30 + z * (8 + z * (1 + z * (28 + z * (36 + z * (2 + z * (35 + z * (7 + z * (21 + z * (15 + z * (0 + z * 32)))))))))))))))))))

def pow3_40_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (13 + z * (13 + z * (15 + z * (24 + z * (4 + z * (27 + z * (33 + z * (0 + z * (38 + z * (6 + z * (19 + z * (19 + z * (14 + z * (14 + z * (39 + z * (8 + z * (25 + z * 4))))))))))))))))))

def pow3_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (13 + z * (3 + z * ((-3) + z * (19 + z * ((-10) + z * ((-18) + z * (17 + z * ((-24) + z * ((-9) + z * (22 + z * ((-5) + z * (2 + z * (41 + z * ((-50) + z * (20 + z * ((-13) + z * ((-14) + z * (0 + z * (29 + z * (25 + z * (4 + z * (8 + z * (12 + z * ((-5) + z * ((-18) + z * (42 + z * (12 + z * (61 + z * ((-1) + z * (3 + z * (32 + z * ((-11) + z * ((-4) + z * (12 + z * (53 + z * (40 + z * (31 + z * (25 + z * 37))))))))))))))))))))))))))))))))))))))

theorem pow3_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_20 z * pow3_20 z = pow3_40_q z * f z + pow3_40 z + (41 : R) * pow3_40_mul_t z := by
  simp only [pow3_20, pow3_40_q, f, pow3_40, pow3_40_mul_t]
  
  ring

theorem pow3_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_20 z * pow3_20 z = pow3_40_q z * f z + pow3_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_40_mul_integer z


theorem pow3_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_20 z * pow3_20 z = pow3_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_40_mul z


theorem pow3_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 40 = pow3_40 z := by
  calc
    _ = u2 z ^ 20 * u2 z ^ 20 := by ring
    _ = pow3_20 z * pow3_20 z := by rw [pow3_20_pow z hz]
    _ = _ := pow3_40_root z hz


def pow3_41 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (35 + z * (24 + z * (19 + z * (15 + z * (18 + z * (10 + z * (35 + z * (35 + z * (6 + z * (11 + z * (30 + z * (0 + z * (27 + z * (14 + z * (18 + z * (19 + z * (32 + z * (4 + z * 12)))))))))))))))))))

def pow3_41_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (36 + z * (1 + z * (5 + z * (11 + z * (38 + z * (25 + z * (0 + z * (36 + z * (15 + z * (27 + z * (19 + z * (6 + z * (8 + z * (14 + z * (9 + z * (22 + z * (21 + z * 26))))))))))))))))))

def pow3_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-34) + z * ((-10) + z * ((-7) + z * (4 + z * ((-15) + z * (25 + z * (32 + z * (8 + z * (34 + z * (20 + z * (43 + z * ((-3) + z * (54 + z * (71 + z * (36 + z * (6 + z * (38 + z * (52 + z * (22 + z * (70 + z * (83 + z * (53 + z * (90 + z * (28 + z * (10 + z * (42 + z * (16 + z * (31 + z * (25 + z * (42 + z * (36 + z * (12 + z * (5 + z * (3 + z * (15 + z * (5 + z * (7 + z * 22))))))))))))))))))))))))))))))))))))))

theorem pow3_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_40 z * u2 z = pow3_41_q z * f z + pow3_41 z + (41 : R) * pow3_41_mul_t z := by
  simp only [pow3_40, u2, pow3_41_q, f, pow3_41, pow3_41_mul_t]
  simp only [pow2_41]
  ring

theorem pow3_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_40 z * u2 z = pow3_41_q z * f z + pow3_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_41_mul_integer z


theorem pow3_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_40 z * u2 z = pow3_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_41_mul z


theorem pow3_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 41 = pow3_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow3_40_pow z hz]
  exact pow3_41_root z hz


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_41 z

theorem iterate3 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 3) = u3 z := by
  calc
    _ = (z ^ (41 ^ 2)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u2 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate2 z hz)
    _ = _ := pow3_41_pow z hz


def pow4_2 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (10 + z * (26 + z * (3 + z * (18 + z * (24 + z * (20 + z * (23 + z * (24 + z * (34 + z * (24 + z * (31 + z * (4 + z * (0 + z * (23 + z * (32 + z * (18 + z * (2 + z * (2 + z * 23)))))))))))))))))))

def pow4_2_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (22 + z * (8 + z * (0 + z * (3 + z * (7 + z * (3 + z * (39 + z * (19 + z * (15 + z * (10 + z * (33 + z * (33 + z * (3 + z * (4 + z * (25 + z * (6 + z * (40 + z * 21))))))))))))))))))

def pow4_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * (31 + z * (35 + z * (54 + z * (40 + z * (50 + z * (57 + z * (46 + z * (87 + z * (54 + z * (65 + z * (34 + z * (25 + z * (66 + z * (58 + z * (46 + z * (43 + z * (41 + z * (58 + z * ((-2) + z * (39 + z * (38 + z * ((-5) + z * ((-15) + z * (26 + z * ((-24) + z * ((-55) + z * ((-33) + z * ((-29) + z * ((-42) + z * ((-2) + z * ((-38) + z * ((-16) + z * ((-26) + z * ((-21) + z * ((-16) + z * ((-19) + z * ((-14) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow4_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z + (41 : R) * pow4_2_mul_t z := by
  simp only [u3, pow4_2_q, f, pow4_2, pow4_2_mul_t]
  simp only [pow3_41]
  ring

theorem pow4_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_2_mul_integer z


theorem pow4_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z * u3 z = pow4_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_2_mul z


theorem pow4_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 2 = pow4_2 z := by
  calc
    _ = u3 z ^ 1 * u3 z ^ 1 := by ring
    _ = u3 z * u3 z := by simp only [pow_one]
    _ = _ := pow4_2_root z hz


def pow4_4 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (35 + z * (20 + z * (16 + z * (24 + z * (35 + z * (27 + z * (10 + z * (6 + z * (4 + z * (28 + z * (7 + z * (32 + z * (6 + z * (37 + z * (28 + z * (23 + z * (23 + z * (22 + z * 2)))))))))))))))))))

def pow4_4_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (35 + z * (39 + z * (38 + z * (18 + z * (11 + z * (25 + z * (37 + z * (1 + z * (33 + z * (39 + z * (34 + z * (32 + z * (12 + z * (17 + z * (16 + z * (36 + z * (7 + z * 37))))))))))))))))))

def pow4_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * ((-29) + z * ((-35) + z * ((-57) + z * ((-39) + z * ((-42) + z * ((-24) + z * ((-37) + z * ((-20) + z * ((-29) + z * ((-32) + z * ((-41) + z * ((-38) + z * ((-37) + z * ((-63) + z * ((-8) + z * ((-41) + z * ((-71) + z * ((-129) + z * ((-57) + z * ((-81) + z * ((-49) + z * ((-91) + z * ((-50) + z * ((-21) + z * ((-58) + z * ((-75) + z * ((-82) + z * ((-80) + z * ((-66) + z * ((-29) + z * ((-59) + z * ((-70) + z * ((-47) + z * ((-23) + z * ((-30) + z * ((-19) + z * ((-25) + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow4_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z + (41 : R) * pow4_4_mul_t z := by
  simp only [pow4_2, pow4_4_q, f, pow4_4, pow4_4_mul_t]
  
  ring

theorem pow4_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_4_mul_integer z


theorem pow4_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_2 z * pow4_2 z = pow4_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_4_mul z


theorem pow4_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 4 = pow4_4 z := by
  calc
    _ = u3 z ^ 2 * u3 z ^ 2 := by ring
    _ = pow4_2 z * pow4_2 z := by rw [pow4_2_pow z hz]
    _ = _ := pow4_4_root z hz


def pow4_5 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (24 + z * (18 + z * (11 + z * (37 + z * (8 + z * (24 + z * (2 + z * (33 + z * (23 + z * (40 + z * (34 + z * (22 + z * (40 + z * (7 + z * (19 + z * (13 + z * (14 + z * (33 + z * 6)))))))))))))))))))

def pow4_5_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (32 + z * (7 + z * (16 + z * (33 + z * (15 + z * (38 + z * (40 + z * (21 + z * (34 + z * (14 + z * (8 + z * (23 + z * (22 + z * (38 + z * (24 + z * (12 + z * (3 + z * 24))))))))))))))))))

def pow4_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-2) + z * (9 + z * (15 + z * ((-4) + z * (21 + z * (26 + z * ((-8) + z * ((-27) + z * ((-12) + z * ((-6) + z * ((-37) + z * (20 + z * ((-1) + z * ((-29) + z * ((-31) + z * ((-46) + z * (0 + z * ((-10) + z * ((-19) + z * ((-40) + z * ((-20) + z * ((-50) + z * ((-40) + z * ((-57) + z * ((-46) + z * ((-54) + z * ((-14) + z * ((-35) + z * ((-20) + z * ((-32) + z * (1 + z * ((-16) + z * ((-16) + z * ((-5) + z * (3 + z * ((-2) + z * ((-11) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow4_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_4 z * u3 z = pow4_5_q z * f z + pow4_5 z + (41 : R) * pow4_5_mul_t z := by
  simp only [pow4_4, u3, pow4_5_q, f, pow4_5, pow4_5_mul_t]
  simp only [pow3_41]
  ring

theorem pow4_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_4 z * u3 z = pow4_5_q z * f z + pow4_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_5_mul_integer z


theorem pow4_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_4 z * u3 z = pow4_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_5_mul z


theorem pow4_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 5 = pow4_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow4_4_pow z hz]
  exact pow4_5_root z hz


def pow4_10 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (34 + z * (13 + z * (19 + z * (1 + z * (20 + z * (10 + z * (34 + z * (6 + z * (21 + z * (2 + z * (21 + z * (36 + z * (18 + z * (12 + z * (4 + z * (10 + z * (28 + z * (14 + z * 12)))))))))))))))))))

def pow4_10_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (17 + z * (21 + z * (29 + z * (37 + z * (17 + z * (7 + z * (7 + z * (38 + z * (24 + z * (27 + z * (15 + z * (5 + z * (4 + z * (6 + z * (7 + z * (9 + z * (13 + z * 36))))))))))))))))))

def pow4_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-15) + z * ((-12) + z * ((-23) + z * ((-37) + z * ((-9) + z * ((-11) + z * (3 + z * ((-26) + z * ((-14) + z * ((-2) + z * ((-6) + z * (41 + z * (40 + z * (107 + z * (39 + z * (54 + z * (58 + z * ((-5) + z * (68 + z * (26 + z * (98 + z * (65 + z * (70 + z * (61 + z * (10 + z * (68 + z * (33 + z * (70 + z * (38 + z * (39 + z * (51 + z * ((-10) + z * ((-13) + z * ((-14) + z * ((-6) + z * (6 + z * ((-17) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow4_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_5 z * pow4_5 z = pow4_10_q z * f z + pow4_10 z + (41 : R) * pow4_10_mul_t z := by
  simp only [pow4_5, pow4_10_q, f, pow4_10, pow4_10_mul_t]
  
  ring

theorem pow4_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_5 z * pow4_5 z = pow4_10_q z * f z + pow4_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_10_mul_integer z


theorem pow4_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_5 z * pow4_5 z = pow4_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_10_mul z


theorem pow4_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 10 = pow4_10 z := by
  calc
    _ = u3 z ^ 5 * u3 z ^ 5 := by ring
    _ = pow4_5 z * pow4_5 z := by rw [pow4_5_pow z hz]
    _ = _ := pow4_10_root z hz


def pow4_20 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (38 + z * (32 + z * (16 + z * (3 + z * (18 + z * (26 + z * (32 + z * (8 + z * (25 + z * (31 + z * (6 + z * (0 + z * (12 + z * (3 + z * (21 + z * (0 + z * (31 + z * (4 + z * 31)))))))))))))))))))

def pow4_20_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (24 + z * (28 + z * (2 + z * (25 + z * (37 + z * (13 + z * (33 + z * (1 + z * (29 + z * (25 + z * (9 + z * (20 + z * (40 + z * (11 + z * (22 + z * (24 + z * (34 + z * 21))))))))))))))))))

def pow4_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * (15 + z * ((-12) + z * (19 + z * ((-34) + z * ((-24) + z * ((-11) + z * ((-17) + z * (11 + z * ((-55) + z * (0 + z * ((-66) + z * (15 + z * ((-20) + z * ((-8) + z * ((-74) + z * ((-91) + z * ((-101) + z * ((-34) + z * ((-46) + z * ((-84) + z * ((-96) + z * ((-69) + z * ((-63) + z * ((-58) + z * ((-57) + z * ((-50) + z * ((-74) + z * ((-73) + z * ((-45) + z * ((-26) + z * ((-49) + z * ((-82) + z * ((-54) + z * ((-34) + z * ((-19) + z * ((-13) + z * ((-8) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow4_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_10 z * pow4_10 z = pow4_20_q z * f z + pow4_20 z + (41 : R) * pow4_20_mul_t z := by
  simp only [pow4_10, pow4_20_q, f, pow4_20, pow4_20_mul_t]
  
  ring

theorem pow4_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_10 z * pow4_10 z = pow4_20_q z * f z + pow4_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_20_mul_integer z


theorem pow4_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_10 z * pow4_10 z = pow4_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_20_mul z


theorem pow4_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 20 = pow4_20 z := by
  calc
    _ = u3 z ^ 10 * u3 z ^ 10 := by ring
    _ = pow4_10 z * pow4_10 z := by rw [pow4_10_pow z hz]
    _ = _ := pow4_20_root z hz


def pow4_40 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (16 + z * (36 + z * (27 + z * (30 + z * (3 + z * (37 + z * (6 + z * (38 + z * (24 + z * (37 + z * (29 + z * (18 + z * (36 + z * (30 + z * (18 + z * (20 + z * (0 + z * (23 + z * 16)))))))))))))))))))

def pow4_40_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (8 + z * (38 + z * (28 + z * (8 + z * (3 + z * (27 + z * (33 + z * (37 + z * (4 + z * (18 + z * (37 + z * (25 + z * (35 + z * (40 + z * (5 + z * (19 + z * (36 + z * 18))))))))))))))))))

def pow4_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (50 + z * (44 + z * (41 + z * (10 + z * (25 + z * (22 + z * (57 + z * (43 + z * (46 + z * (31 + z * (30 + z * (8 + z * ((-40) + z * ((-71) + z * ((-32) + z * ((-20) + z * ((-44) + z * ((-105) + z * ((-26) + z * ((-12) + z * ((-111) + z * ((-94) + z * ((-86) + z * ((-58) + z * ((-91) + z * ((-56) + z * ((-88) + z * ((-83) + z * ((-87) + z * ((-80) + z * ((-95) + z * ((-53) + z * ((-79) + z * (8 + z * ((-33) + z * (13 + z * ((-8) + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow4_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_20 z * pow4_20 z = pow4_40_q z * f z + pow4_40 z + (41 : R) * pow4_40_mul_t z := by
  simp only [pow4_20, pow4_40_q, f, pow4_40, pow4_40_mul_t]
  
  ring

theorem pow4_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_20 z * pow4_20 z = pow4_40_q z * f z + pow4_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_40_mul_integer z


theorem pow4_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_20 z * pow4_20 z = pow4_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_40_mul z


theorem pow4_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 40 = pow4_40 z := by
  calc
    _ = u3 z ^ 20 * u3 z ^ 20 := by ring
    _ = pow4_20 z * pow4_20 z := by rw [pow4_20_pow z hz]
    _ = _ := pow4_40_root z hz


def pow4_41 {R : Type*} [CommRing R] (z : R) : R := (12 + z * (11 + z * (4 + z * (18 + z * (23 + z * (39 + z * (40 + z * (20 + z * (28 + z * (8 + z * (27 + z * (39 + z * (16 + z * (18 + z * (31 + z * (32 + z * (25 + z * (34 + z * (37 + z * 22)))))))))))))))))))

def pow4_41_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (25 + z * (40 + z * (29 + z * (37 + z * (22 + z * (10 + z * (28 + z * (20 + z * (39 + z * (6 + z * (5 + z * (5 + z * (17 + z * (18 + z * (23 + z * (40 + z * (33 + z * 28))))))))))))))))))

def pow4_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * (7 + z * ((-3) + z * (19 + z * ((-7) + z * (2 + z * (12 + z * (10 + z * (28 + z * (7 + z * (58 + z * (41 + z * (34 + z * (61 + z * (59 + z * (40 + z * ((-6) + z * (7 + z * ((-40) + z * (13 + z * ((-35) + z * (23 + z * ((-13) + z * ((-6) + z * ((-30) + z * ((-5) + z * (9 + z * (13 + z * ((-29) + z * (5 + z * ((-11) + z * ((-35) + z * ((-56) + z * ((-55) + z * ((-50) + z * ((-28) + z * ((-22) + z * ((-13) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow4_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_40 z * u3 z = pow4_41_q z * f z + pow4_41 z + (41 : R) * pow4_41_mul_t z := by
  simp only [pow4_40, u3, pow4_41_q, f, pow4_41, pow4_41_mul_t]
  simp only [pow3_41]
  ring

theorem pow4_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_40 z * u3 z = pow4_41_q z * f z + pow4_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_41_mul_integer z


theorem pow4_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_40 z * u3 z = pow4_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_41_mul z


theorem pow4_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 41 = pow4_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow4_40_pow z hz]
  exact pow4_41_root z hz


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_41 z

theorem iterate4 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 4) = u4 z := by
  calc
    _ = (z ^ (41 ^ 3)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u3 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate3 z hz)
    _ = _ := pow4_41_pow z hz

end DimensionTen.Mod41

end

end OAI
