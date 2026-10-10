import OAI.Analysis.Quantum.DimensionTen.Mod41Powers09

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow19_2 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (39 + z * (34 + z * (14 + z * (14 + z * (15 + z * (25 + z * (2 + z * (10 + z * (31 + z * (12 + z * (31 + z * (0 + z * (23 + z * (24 + z * (2 + z * (32 + z * (17 + z * (5 + z * 32)))))))))))))))))))

def pow19_2_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (0 + z * (38 + z * (9 + z * (31 + z * (28 + z * (33 + z * (12 + z * (13 + z * (34 + z * (14 + z * (33 + z * (24 + z * (34 + z * (15 + z * (18 + z * (34 + z * (29 + z * 21))))))))))))))))))

def pow19_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-34) + z * ((-6) + z * ((-32) + z * (39 + z * ((-9) + z * (33 + z * (12 + z * (31 + z * (46 + z * ((-6) + z * (12 + z * ((-57) + z * ((-22) + z * ((-96) + z * ((-53) + z * ((-102) + z * ((-125) + z * ((-100) + z * ((-85) + z * ((-95) + z * ((-98) + z * ((-56) + z * ((-63) + z * ((-95) + z * ((-85) + z * ((-110) + z * ((-84) + z * ((-116) + z * ((-108) + z * ((-90) + z * ((-86) + z * ((-72) + z * ((-63) + z * ((-55) + z * ((-39) + z * (0 + z * ((-16) + z * ((-9) + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow19_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z + (41 : R) * pow19_2_mul_t z := by
  simp only [u18, pow19_2_q, f, pow19_2, pow19_2_mul_t]
  simp only [pow18_41]
  ring

theorem pow19_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_2_mul_integer z


theorem pow19_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z * u18 z = pow19_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_2_mul z


theorem pow19_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 2 = pow19_2 z := by
  calc
    _ = u18 z ^ 1 * u18 z ^ 1 := by ring
    _ = u18 z * u18 z := by simp only [pow_one]
    _ = _ := pow19_2_root z hz


def pow19_4 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (18 + z * (36 + z * (5 + z * (21 + z * (32 + z * (35 + z * (27 + z * (31 + z * (16 + z * (14 + z * (21 + z * (17 + z * (2 + z * (2 + z * (12 + z * (39 + z * (22 + z * (27 + z * 28)))))))))))))))))))

def pow19_4_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (32 + z * (25 + z * (29 + z * (14 + z * (18 + z * (9 + z * (33 + z * (12 + z * (28 + z * (10 + z * (26 + z * (1 + z * (5 + z * (22 + z * (26 + z * (19 + z * (22 + z * 40))))))))))))))))))

def pow19_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (0 + z * (29 + z * (18 + z * (24 + z * ((-7) + z * (26 + z * (11 + z * ((-2) + z * ((-33) + z * (27 + z * (5 + z * (30 + z * ((-1) + z * (15 + z * (19 + z * ((-28) + z * ((-5) + z * ((-60) + z * ((-12) + z * (9 + z * ((-26) + z * ((-30) + z * ((-30) + z * ((-29) + z * ((-17) + z * ((-71) + z * (11 + z * ((-7) + z * ((-35) + z * (13 + z * ((-45) + z * ((-18) + z * ((-26) + z * ((-54) + z * (8 + z * ((-6) + z * ((-22) + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow19_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z + (41 : R) * pow19_4_mul_t z := by
  simp only [pow19_2, pow19_4_q, f, pow19_4, pow19_4_mul_t]
  
  ring

theorem pow19_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_4_mul_integer z


theorem pow19_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_2 z * pow19_2 z = pow19_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_4_mul z


theorem pow19_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 4 = pow19_4 z := by
  calc
    _ = u18 z ^ 2 * u18 z ^ 2 := by ring
    _ = pow19_2 z * pow19_2 z := by rw [pow19_2_pow z hz]
    _ = _ := pow19_4_root z hz


def pow19_5 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (2 + z * (8 + z * (32 + z * (24 + z * (29 + z * (31 + z * (6 + z * (4 + z * (5 + z * (3 + z * (15 + z * (37 + z * (13 + z * (12 + z * (10 + z * (12 + z * (30 + z * (40 + z * 6)))))))))))))))))))

def pow19_5_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (37 + z * (38 + z * (13 + z * (21 + z * (39 + z * (21 + z * (20 + z * (25 + z * (5 + z * (35 + z * (18 + z * (11 + z * (5 + z * (25 + z * (38 + z * (1 + z * (15 + z * 33))))))))))))))))))

def pow19_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-23) + z * ((-27) + z * (6 + z * ((-13) + z * ((-9) + z * (3 + z * (41 + z * (14 + z * (21 + z * (6 + z * (19 + z * ((-30) + z * (16 + z * ((-32) + z * ((-83) + z * ((-74) + z * ((-70) + z * ((-55) + z * ((-62) + z * ((-29) + z * ((-3) + z * ((-54) + z * (2 + z * ((-3) + z * ((-52) + z * ((-57) + z * ((-26) + z * ((-26) + z * ((-75) + z * ((-45) + z * ((-24) + z * ((-20) + z * ((-37) + z * ((-18) + z * (33 + z * (1 + z * ((-2) + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow19_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_4 z * u18 z = pow19_5_q z * f z + pow19_5 z + (41 : R) * pow19_5_mul_t z := by
  simp only [pow19_4, u18, pow19_5_q, f, pow19_5, pow19_5_mul_t]
  simp only [pow18_41]
  ring

theorem pow19_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_4 z * u18 z = pow19_5_q z * f z + pow19_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_5_mul_integer z


theorem pow19_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_4 z * u18 z = pow19_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_5_mul z


theorem pow19_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 5 = pow19_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow19_4_pow z hz]
  exact pow19_5_root z hz


def pow19_10 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (2 + z * (22 + z * (11 + z * (8 + z * (17 + z * (15 + z * (1 + z * (33 + z * (36 + z * (23 + z * (40 + z * (3 + z * (38 + z * (35 + z * (16 + z * (10 + z * (11 + z * (37 + z * 35)))))))))))))))))))

def pow19_10_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (4 + z * (34 + z * (12 + z * (22 + z * (29 + z * (21 + z * (27 + z * (6 + z * (1 + z * (18 + z * (13 + z * (15 + z * (27 + z * (30 + z * (23 + z * (37 + z * (15 + z * 36))))))))))))))))))

def pow19_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-14) + z * ((-54) + z * ((-9) + z * ((-60) + z * ((-21) + z * ((-20) + z * ((-40) + z * (3 + z * ((-1) + z * ((-13) + z * ((-38) + z * ((-39) + z * ((-75) + z * ((-90) + z * ((-58) + z * ((-77) + z * ((-52) + z * ((-78) + z * ((-81) + z * ((-62) + z * ((-30) + z * ((-36) + z * ((-4) + z * ((-11) + z * ((-81) + z * ((-74) + z * ((-62) + z * ((-50) + z * ((-30) + z * ((-8) + z * ((-46) + z * ((-65) + z * ((-56) + z * ((-22) + z * (8 + z * (21 + z * ((-15) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow19_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_5 z * pow19_5 z = pow19_10_q z * f z + pow19_10 z + (41 : R) * pow19_10_mul_t z := by
  simp only [pow19_5, pow19_10_q, f, pow19_10, pow19_10_mul_t]
  
  ring

theorem pow19_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_5 z * pow19_5 z = pow19_10_q z * f z + pow19_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_10_mul_integer z


theorem pow19_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_5 z * pow19_5 z = pow19_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_10_mul z


theorem pow19_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 10 = pow19_10 z := by
  calc
    _ = u18 z ^ 5 * u18 z ^ 5 := by ring
    _ = pow19_5 z * pow19_5 z := by rw [pow19_5_pow z hz]
    _ = _ := pow19_10_root z hz


def pow19_20 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (35 + z * (6 + z * (5 + z * (1 + z * (37 + z * (25 + z * (34 + z * (28 + z * (38 + z * (22 + z * (23 + z * (34 + z * (34 + z * (39 + z * (7 + z * (40 + z * (12 + z * (39 + z * 7)))))))))))))))))))

def pow19_20_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (14 + z * (19 + z * (2 + z * (21 + z * (7 + z * (16 + z * (34 + z * (8 + z * (24 + z * (12 + z * (22 + z * (2 + z * (26 + z * (12 + z * (27 + z * (15 + z * (34 + z * 36))))))))))))))))))

def pow19_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-13) + z * (8 + z * (2 + z * ((-15) + z * (13 + z * ((-11) + z * ((-28) + z * (18 + z * ((-4) + z * (33 + z * (32 + z * (5 + z * (56 + z * (54 + z * (2 + z * (36 + z * ((-4) + z * (25 + z * (94 + z * (28 + z * (48 + z * (61 + z * (58 + z * (77 + z * (3 + z * (30 + z * (117 + z * (70 + z * (50 + z * (25 + z * (19 + z * (36 + z * (6 + z * ((-26) + z * ((-9) + z * (12 + z * (36 + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow19_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_10 z * pow19_10 z = pow19_20_q z * f z + pow19_20 z + (41 : R) * pow19_20_mul_t z := by
  simp only [pow19_10, pow19_20_q, f, pow19_20, pow19_20_mul_t]
  
  ring

theorem pow19_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_10 z * pow19_10 z = pow19_20_q z * f z + pow19_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_20_mul_integer z


theorem pow19_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_10 z * pow19_10 z = pow19_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_20_mul z


theorem pow19_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 20 = pow19_20 z := by
  calc
    _ = u18 z ^ 10 * u18 z ^ 10 := by ring
    _ = pow19_10 z * pow19_10 z := by rw [pow19_10_pow z hz]
    _ = _ := pow19_20_root z hz


def pow19_40 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (21 + z * (0 + z * (12 + z * (4 + z * (12 + z * (32 + z * (18 + z * (3 + z * (19 + z * (5 + z * (19 + z * (27 + z * (8 + z * (19 + z * (30 + z * (3 + z * (39 + z * (32 + z * 30)))))))))))))))))))

def pow19_40_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (10 + z * (36 + z * (29 + z * (37 + z * (13 + z * (9 + z * (23 + z * (33 + z * (16 + z * (19 + z * (10 + z * (28 + z * (23 + z * (29 + z * (35 + z * (40 + z * (19 + z * 8))))))))))))))))))

def pow19_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * (8 + z * ((-27) + z * ((-31) + z * ((-87) + z * ((-24) + z * (14 + z * ((-9) + z * ((-5) + z * ((-4) + z * (21 + z * ((-11) + z * (20 + z * (67 + z * (68 + z * (28 + z * ((-1) + z * (55 + z * (50 + z * (89 + z * (48 + z * (108 + z * (74 + z * (118 + z * (93 + z * (127 + z * (86 + z * (71 + z * (60 + z * (32 + z * (53 + z * ((-10) + z * (26 + z * ((-31) + z * (22 + z * ((-6) + z * (23 + z * (7 + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow19_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_20 z * pow19_20 z = pow19_40_q z * f z + pow19_40 z + (41 : R) * pow19_40_mul_t z := by
  simp only [pow19_20, pow19_40_q, f, pow19_40, pow19_40_mul_t]
  
  ring

theorem pow19_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_20 z * pow19_20 z = pow19_40_q z * f z + pow19_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_40_mul_integer z


theorem pow19_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_20 z * pow19_20 z = pow19_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_40_mul z


theorem pow19_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 40 = pow19_40 z := by
  calc
    _ = u18 z ^ 20 * u18 z ^ 20 := by ring
    _ = pow19_20 z * pow19_20 z := by rw [pow19_20_pow z hz]
    _ = _ := pow19_40_root z hz


def pow19_41 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (10 + z * (32 + z * (2 + z * (10 + z * (31 + z * (9 + z * (27 + z * (26 + z * (19 + z * (31 + z * (13 + z * (16 + z * (17 + z * (36 + z * (16 + z * (26 + z * (1 + z * (14 + z * 3)))))))))))))))))))

def pow19_41_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (23 + z * (14 + z * (9 + z * (24 + z * (26 + z * (35 + z * (36 + z * (0 + z * (1 + z * (32 + z * (29 + z * (3 + z * (40 + z * (12 + z * (6 + z * (35 + z * (29 + z * 9))))))))))))))))))

def pow19_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-2) + z * (13 + z * (8 + z * ((-6) + z * ((-14) + z * ((-16) + z * ((-9) + z * (2 + z * ((-9) + z * ((-14) + z * ((-31) + z * ((-10) + z * ((-37) + z * ((-34) + z * ((-53) + z * ((-11) + z * ((-63) + z * ((-62) + z * (21 + z * ((-19) + z * ((-67) + z * ((-10) + z * ((-37) + z * ((-43) + z * ((-44) + z * ((-44) + z * ((-54) + z * ((-42) + z * ((-58) + z * ((-26) + z * ((-11) + z * ((-61) + z * ((-4) + z * (20 + z * ((-4) + z * (13 + z * (19 + z * 21))))))))))))))))))))))))))))))))))))))

theorem pow19_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_40 z * u18 z = pow19_41_q z * f z + pow19_41 z + (41 : R) * pow19_41_mul_t z := by
  simp only [pow19_40, u18, pow19_41_q, f, pow19_41, pow19_41_mul_t]
  simp only [pow18_41]
  ring

theorem pow19_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_40 z * u18 z = pow19_41_q z * f z + pow19_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_41_mul_integer z


theorem pow19_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_40 z * u18 z = pow19_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_41_mul z


theorem pow19_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 41 = pow19_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow19_40_pow z hz]
  exact pow19_41_root z hz


abbrev u19 {R : Type*} [CommRing R] (z : R) : R := pow19_41 z

theorem iterate19 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 19) = u19 z := by
  calc
    _ = (z ^ (41 ^ 18)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u18 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate18 z hz)
    _ = _ := pow19_41_pow z hz


def pow20_2 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * (14 + z * (21 + z * (5 + z * (21 + z * (35 + z * (7 + z * (29 + z * (11 + z * (15 + z * (12 + z * (26 + z * (10 + z * (27 + z * (1 + z * (2 + z * (22 + z * (36 + z * 12)))))))))))))))))))

def pow20_2_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (22 + z * (1 + z * (17 + z * (12 + z * (21 + z * (14 + z * (14 + z * (27 + z * (6 + z * (32 + z * (8 + z * (31 + z * (16 + z * (34 + z * (32 + z * (12 + z * (19 + z * 9))))))))))))))))))

def pow20_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-22) + z * ((-8) + z * ((-16) + z * ((-2) + z * ((-36) + z * (1 + z * (2 + z * ((-36) + z * (18 + z * (0 + z * (3 + z * ((-10) + z * (16 + z * ((-21) + z * (1 + z * (1 + z * ((-17) + z * (14 + z * ((-26) + z * (12 + z * (9 + z * ((-24) + z * (9 + z * ((-11) + z * ((-32) + z * ((-22) + z * ((-42) + z * ((-20) + z * ((-58) + z * ((-32) + z * ((-62) + z * ((-32) + z * ((-51) + z * ((-27) + z * ((-18) + z * ((-13) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow20_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u19 z * u19 z = pow20_2_q z * f z + pow20_2 z + (41 : R) * pow20_2_mul_t z := by
  simp only [u19, pow20_2_q, f, pow20_2, pow20_2_mul_t]
  simp only [pow19_41]
  ring

theorem pow20_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u19 z * u19 z = pow20_2_q z * f z + pow20_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_2_mul_integer z


theorem pow20_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z * u19 z = pow20_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_2_mul z


theorem pow20_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 2 = pow20_2 z := by
  calc
    _ = u19 z ^ 1 * u19 z ^ 1 := by ring
    _ = u19 z * u19 z := by simp only [pow_one]
    _ = _ := pow20_2_root z hz


def pow20_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (25 + z * (14 + z * (1 + z * (38 + z * (7 + z * (18 + z * (11 + z * (0 + z * (13 + z * (24 + z * (17 + z * (10 + z * (36 + z * (16 + z * (16 + z * (24 + z * (15 + z * (34 + z * 36)))))))))))))))))))

def pow20_4_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (4 + z * (8 + z * (1 + z * (21 + z * (0 + z * (38 + z * (15 + z * (36 + z * (9 + z * (23 + z * (34 + z * (28 + z * (38 + z * (3 + z * (7 + z * (23 + z * (29 + z * 21))))))))))))))))))

def pow20_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-4) + z * ((-20) + z * (20 + z * ((-31) + z * (19 + z * (1 + z * ((-7) + z * ((-29) + z * (24 + z * ((-34) + z * ((-16) + z * ((-18) + z * ((-35) + z * (2 + z * ((-64) + z * ((-43) + z * ((-58) + z * ((-33) + z * ((-44) + z * ((-10) + z * ((-54) + z * ((-45) + z * ((-46) + z * ((-31) + z * ((-68) + z * ((-31) + z * ((-87) + z * ((-66) + z * ((-54) + z * ((-27) + z * ((-24) + z * ((-36) + z * ((-41) + z * ((-32) + z * ((-1) + z * (14 + z * (5 + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow20_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_2 z * pow20_2 z = pow20_4_q z * f z + pow20_4 z + (41 : R) * pow20_4_mul_t z := by
  simp only [pow20_2, pow20_4_q, f, pow20_4, pow20_4_mul_t]
  
  ring

theorem pow20_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_2 z * pow20_2 z = pow20_4_q z * f z + pow20_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_4_mul_integer z


theorem pow20_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_2 z * pow20_2 z = pow20_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_4_mul z


theorem pow20_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 4 = pow20_4 z := by
  calc
    _ = u19 z ^ 2 * u19 z ^ 2 := by ring
    _ = pow20_2 z * pow20_2 z := by rw [pow20_2_pow z hz]
    _ = _ := pow20_4_root z hz


def pow20_5 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (30 + z * (29 + z * (24 + z * (25 + z * (20 + z * (34 + z * (1 + z * (16 + z * (12 + z * (34 + z * (9 + z * (19 + z * (7 + z * (20 + z * (31 + z * (26 + z * (29 + z * (3 + z * 34)))))))))))))))))))

def pow20_5_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (9 + z * (29 + z * (19 + z * (39 + z * (14 + z * (2 + z * (34 + z * (33 + z * (22 + z * (38 + z * (39 + z * (20 + z * (6 + z * (32 + z * (18 + z * (5 + z * (31 + z * 26))))))))))))))))))

def pow20_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-5) + z * ((-22) + z * ((-10) + z * ((-45) + z * ((-29) + z * ((-3) + z * ((-32) + z * ((-37) + z * ((-32) + z * ((-56) + z * ((-56) + z * ((-57) + z * ((-37) + z * ((-50) + z * ((-43) + z * ((-44) + z * ((-52) + z * ((-78) + z * ((-88) + z * ((-2) + z * ((-59) + z * ((-79) + z * ((-26) + z * ((-28) + z * ((-59) + z * ((-48) + z * ((-20) + z * ((-26) + z * ((-26) + z * ((-26) + z * ((-4) + z * ((-1) + z * ((-20) + z * ((-9) + z * ((-1) + z * ((-20) + z * ((-5) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow20_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_4 z * u19 z = pow20_5_q z * f z + pow20_5 z + (41 : R) * pow20_5_mul_t z := by
  simp only [pow20_4, u19, pow20_5_q, f, pow20_5, pow20_5_mul_t]
  simp only [pow19_41]
  ring

theorem pow20_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_4 z * u19 z = pow20_5_q z * f z + pow20_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_5_mul_integer z


theorem pow20_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_4 z * u19 z = pow20_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_5_mul z


theorem pow20_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 5 = pow20_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow20_4_pow z hz]
  exact pow20_5_root z hz


def pow20_10 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (13 + z * (22 + z * (27 + z * (2 + z * (6 + z * (30 + z * (18 + z * (6 + z * (40 + z * (6 + z * (21 + z * (20 + z * (8 + z * (36 + z * (35 + z * (29 + z * (36 + z * (18 + z * 19)))))))))))))))))))

def pow20_10_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (6 + z * (34 + z * (5 + z * (4 + z * (24 + z * (19 + z * (9 + z * (36 + z * (36 + z * (24 + z * (6 + z * (31 + z * (18 + z * (35 + z * (23 + z * (14 + z * (5 + z * 8))))))))))))))))))

def pow20_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-3) + z * ((-24) + z * (33 + z * (8 + z * (44 + z * (39 + z * (37 + z * (19 + z * ((-16) + z * ((-4) + z * (28 + z * (3 + z * ((-12) + z * ((-11) + z * ((-8) + z * ((-15) + z * ((-5) + z * (50 + z * (7 + z * (72 + z * (35 + z * (27 + z * ((-4) + z * ((-38) + z * (10 + z * ((-31) + z * ((-3) + z * ((-36) + z * (16 + z * ((-12) + z * (15 + z * (13 + z * (20 + z * (43 + z * (30 + z * (41 + z * ((-1) + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow20_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_5 z * pow20_5 z = pow20_10_q z * f z + pow20_10 z + (41 : R) * pow20_10_mul_t z := by
  simp only [pow20_5, pow20_10_q, f, pow20_10, pow20_10_mul_t]
  
  ring

theorem pow20_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_5 z * pow20_5 z = pow20_10_q z * f z + pow20_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_10_mul_integer z


theorem pow20_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_5 z * pow20_5 z = pow20_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_10_mul z


theorem pow20_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 10 = pow20_10 z := by
  calc
    _ = u19 z ^ 5 * u19 z ^ 5 := by ring
    _ = pow20_5 z * pow20_5 z := by rw [pow20_5_pow z hz]
    _ = _ := pow20_10_root z hz


def pow20_20 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (14 + z * (31 + z * (14 + z * (27 + z * (8 + z * (11 + z * (38 + z * (39 + z * (34 + z * (32 + z * (35 + z * (5 + z * (25 + z * (39 + z * (19 + z * (37 + z * (24 + z * (40 + z * 11)))))))))))))))))))

def pow20_20_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (10 + z * (12 + z * (36 + z * (28 + z * (29 + z * (1 + z * (13 + z * (18 + z * (13 + z * (34 + z * (0 + z * (33 + z * (18 + z * (30 + z * (9 + z * (20 + z * (22 + z * 33))))))))))))))))))

def pow20_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-18) + z * ((-32) + z * ((-26) + z * ((-43) + z * ((-42) + z * ((-15) + z * ((-61) + z * ((-21) + z * ((-9) + z * ((-43) + z * ((-37) + z * ((-37) + z * ((-18) + z * ((-80) + z * ((-9) + z * ((-46) + z * ((-7) + z * ((-1) + z * ((-52) + z * (14 + z * (19 + z * ((-6) + z * (50 + z * (26 + z * (28 + z * (52 + z * (11 + z * (31 + z * (6 + z * (48 + z * (46 + z * (34 + z * (31 + z * (35 + z * (16 + z * (11 + z * ((-8) + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow20_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_10 z * pow20_10 z = pow20_20_q z * f z + pow20_20 z + (41 : R) * pow20_20_mul_t z := by
  simp only [pow20_10, pow20_20_q, f, pow20_20, pow20_20_mul_t]
  
  ring

theorem pow20_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_10 z * pow20_10 z = pow20_20_q z * f z + pow20_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_20_mul_integer z


theorem pow20_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_10 z * pow20_10 z = pow20_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_20_mul z


theorem pow20_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 20 = pow20_20 z := by
  calc
    _ = u19 z ^ 10 * u19 z ^ 10 := by ring
    _ = pow20_10 z * pow20_10 z := by rw [pow20_10_pow z hz]
    _ = _ := pow20_20_root z hz


def pow20_40 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (6 + z * (10 + z * (31 + z * (23 + z * (22 + z * (37 + z * (24 + z * (39 + z * (34 + z * (20 + z * (35 + z * (28 + z * (24 + z * (31 + z * (17 + z * (37 + z * (1 + z * (16 + z * 1)))))))))))))))))))

def pow20_40_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (8 + z * (33 + z * (25 + z * (21 + z * (33 + z * (11 + z * (4 + z * (18 + z * (36 + z * (32 + z * (26 + z * (23 + z * (11 + z * (27 + z * (10 + z * (38 + z * (38 + z * 39))))))))))))))))))

def pow20_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * ((-2) + z * ((-16) + z * ((-8) + z * ((-11) + z * ((-18) + z * ((-5) + z * ((-3) + z * (33 + z * (22 + z * (37 + z * (61 + z * (33 + z * (39 + z * (47 + z * (99 + z * (55 + z * (78 + z * (97 + z * (65 + z * (80 + z * (80 + z * (103 + z * (99 + z * (96 + z * (104 + z * (96 + z * (85 + z * (34 + z * (37 + z * (28 + z * (23 + z * (32 + z * ((-9) + z * (20 + z * (1 + z * (7 + z * ((-8) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow20_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_20 z * pow20_20 z = pow20_40_q z * f z + pow20_40 z + (41 : R) * pow20_40_mul_t z := by
  simp only [pow20_20, pow20_40_q, f, pow20_40, pow20_40_mul_t]
  
  ring

theorem pow20_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_20 z * pow20_20 z = pow20_40_q z * f z + pow20_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_40_mul_integer z


theorem pow20_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_20 z * pow20_20 z = pow20_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_40_mul z


theorem pow20_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 40 = pow20_40 z := by
  calc
    _ = u19 z ^ 20 * u19 z ^ 20 := by ring
    _ = pow20_20 z * pow20_20 z := by rw [pow20_20_pow z hz]
    _ = _ := pow20_40_root z hz


abbrev pow20_41 {R : Type*} [CommRing R] (z : R) : R := u0 z

def pow20_41_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (10 + z * (37 + z * (11 + z * (21 + z * (10 + z * (28 + z * (30 + z * (21 + z * (40 + z * (21 + z * (40 + z * (0 + z * (18 + z * (18 + z * (35 + z * (33 + z * (13 + z * 3))))))))))))))))))

def pow20_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-11) + z * ((-36) + z * ((-16) + z * ((-44) + z * (14 + z * ((-32) + z * ((-16) + z * (2 + z * ((-32) + z * (8 + z * ((-25) + z * (26 + z * (15 + z * (43 + z * ((-8) + z * (24 + z * ((-10) + z * (11 + z * (16 + z * (22 + z * (25 + z * (11 + z * (6 + z * ((-1) + z * ((-26) + z * ((-25) + z * ((-24) + z * ((-17) + z * ((-19) + z * ((-30) + z * ((-40) + z * ((-29) + z * ((-43) + z * ((-25) + z * ((-28) + z * ((-6) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow20_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_40 z * u19 z = pow20_41_q z * f z + pow20_41 z + (41 : R) * pow20_41_mul_t z := by
  simp only [pow20_40, u19, pow20_41_q, f, pow20_41, pow20_41_mul_t]
  simp only [pow19_41, u0]
  ring

theorem pow20_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_40 z * u19 z = pow20_41_q z * f z + pow20_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_41_mul_integer z


theorem pow20_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_40 z * u19 z = pow20_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_41_mul z


theorem pow20_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 41 = pow20_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow20_40_pow z hz]
  exact pow20_41_root z hz


abbrev u20 {R : Type*} [CommRing R] (z : R) : R := u0 z

theorem iterate20 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 20) = u20 z := by
  calc
    _ = (z ^ (41 ^ 19)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u19 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate19 z hz)
    _ = _ := pow20_41_pow z hz

end DimensionTen.Mod41

end

end OAI
