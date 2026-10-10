import OAI.Analysis.Quantum.DimensionTen.Mod41Powers05

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow11_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (2 + z * (21 + z * (15 + z * (17 + z * (22 + z * (33 + z * (23 + z * (12 + z * (35 + z * (25 + z * (38 + z * (19 + z * (29 + z * (3 + z * (20 + z * (26 + z * (11 + z * (0 + z * 12)))))))))))))))))))

def pow11_2_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (16 + z * (28 + z * (36 + z * (11 + z * (15 + z * (40 + z * (29 + z * (9 + z * (7 + z * (23 + z * (12 + z * (27 + z * (5 + z * (36 + z * (36 + z * (15 + z * (6 + z * 25))))))))))))))))))

def pow11_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-23) + z * ((-34) + z * ((-34) + z * ((-40) + z * ((-4) + z * ((-55) + z * ((-33) + z * ((-33) + z * ((-8) + z * ((-57) + z * ((-53) + z * ((-35) + z * ((-25) + z * ((-84) + z * ((-92) + z * ((-105) + z * ((-112) + z * ((-117) + z * ((-130) + z * ((-100) + z * ((-106) + z * ((-123) + z * ((-94) + z * ((-78) + z * ((-115) + z * ((-89) + z * ((-58) + z * ((-69) + z * ((-107) + z * ((-86) + z * ((-70) + z * ((-55) + z * ((-70) + z * ((-53) + z * ((-23) + z * ((-10) + z * ((-16) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z + (41 : R) * pow11_2_mul_t z := by
  simp only [u10, pow11_2_q, f, pow11_2, pow11_2_mul_t]
  simp only [pow10_41]
  ring

theorem pow11_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_2_mul_integer z


theorem pow11_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z * u10 z = pow11_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_2_mul z


theorem pow11_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 2 = pow11_2 z := by
  calc
    _ = u10 z ^ 1 * u10 z ^ 1 := by ring
    _ = u10 z * u10 z := by simp only [pow_one]
    _ = _ := pow11_2_root z hz


def pow11_4 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (5 + z * (8 + z * (17 + z * (26 + z * (16 + z * (11 + z * (10 + z * (38 + z * (27 + z * (26 + z * (25 + z * (38 + z * (31 + z * (39 + z * (3 + z * (1 + z * (0 + z * (13 + z * 15)))))))))))))))))))

def pow11_4_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (16 + z * (7 + z * (25 + z * (25 + z * (33 + z * (39 + z * (40 + z * (4 + z * (18 + z * (31 + z * (28 + z * (12 + z * (14 + z * (40 + z * (18 + z * (29 + z * (26 + z * 21))))))))))))))))))

def pow11_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-24) + z * ((-34) + z * ((-35) + z * ((-48) + z * ((-55) + z * ((-47) + z * ((-80) + z * ((-38) + z * ((-32) + z * ((-40) + z * ((-47) + z * ((-7) + z * (5 + z * ((-48) + z * ((-4) + z * ((-31) + z * ((-26) + z * ((-46) + z * ((-20) + z * ((-21) + z * ((-42) + z * ((-19) + z * ((-32) + z * ((-35) + z * ((-61) + z * ((-32) + z * ((-29) + z * ((-35) + z * ((-64) + z * ((-60) + z * ((-59) + z * ((-52) + z * ((-77) + z * ((-43) + z * ((-29) + z * ((-22) + z * ((-16) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow11_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z + (41 : R) * pow11_4_mul_t z := by
  simp only [pow11_2, pow11_4_q, f, pow11_4, pow11_4_mul_t]
  
  ring

theorem pow11_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_4_mul_integer z


theorem pow11_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_2 z * pow11_2 z = pow11_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_4_mul z


theorem pow11_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 4 = pow11_4 z := by
  calc
    _ = u10 z ^ 2 * u10 z ^ 2 := by ring
    _ = pow11_2 z * pow11_2 z := by rw [pow11_2_pow z hz]
    _ = _ := pow11_4_root z hz


def pow11_5 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (33 + z * (13 + z * (11 + z * (16 + z * (27 + z * (33 + z * (14 + z * (24 + z * (30 + z * (15 + z * (6 + z * (21 + z * (15 + z * (32 + z * (30 + z * (9 + z * (11 + z * (19 + z * 5)))))))))))))))))))

def pow11_5_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (33 + z * (30 + z * (30 + z * (24 + z * (21 + z * (9 + z * (25 + z * (14 + z * (40 + z * (21 + z * (18 + z * (8 + z * (6 + z * (19 + z * (27 + z * (5 + z * (15 + z * 34))))))))))))))))))

def pow11_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-27) + z * ((-25) + z * ((-36) + z * ((-22) + z * ((-29) + z * ((-30) + z * ((-17) + z * ((-1) + z * ((-41) + z * ((-25) + z * ((-41) + z * ((-12) + z * (6 + z * (1 + z * ((-33) + z * ((-46) + z * ((-41) + z * ((-71) + z * ((-61) + z * ((-95) + z * ((-39) + z * ((-69) + z * ((-41) + z * ((-67) + z * ((-79) + z * ((-58) + z * ((-23) + z * ((-53) + z * ((-68) + z * ((-51) + z * ((-29) + z * ((-37) + z * ((-56) + z * ((-56) + z * ((-26) + z * ((-18) + z * ((-20) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow11_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_4 z * u10 z = pow11_5_q z * f z + pow11_5 z + (41 : R) * pow11_5_mul_t z := by
  simp only [pow11_4, u10, pow11_5_q, f, pow11_5, pow11_5_mul_t]
  simp only [pow10_41]
  ring

theorem pow11_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_4 z * u10 z = pow11_5_q z * f z + pow11_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_5_mul_integer z


theorem pow11_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_4 z * u10 z = pow11_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_5_mul z


theorem pow11_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 5 = pow11_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow11_4_pow z hz]
  exact pow11_5_root z hz


def pow11_10 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (2 + z * (0 + z * (22 + z * (10 + z * (31 + z * (7 + z * (24 + z * (15 + z * (1 + z * (3 + z * (38 + z * (1 + z * (19 + z * (30 + z * (28 + z * (36 + z * (19 + z * (21 + z * 25)))))))))))))))))))

def pow11_10_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (13 + z * (27 + z * (27 + z * (40 + z * (24 + z * (27 + z * (3 + z * (21 + z * (33 + z * (1 + z * (7 + z * (30 + z * (26 + z * (5 + z * (9 + z * (36 + z * (14 + z * 25))))))))))))))))))

def pow11_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * (33 + z * (12 + z * ((-6) + z * ((-25) + z * (5 + z * (19 + z * (38 + z * (9 + z * (36 + z * (43 + z * (18 + z * (13 + z * ((-2) + z * (67 + z * (75 + z * ((-9) + z * ((-8) + z * (9 + z * ((-4) + z * ((-51) + z * ((-1) + z * ((-6) + z * ((-17) + z * ((-5) + z * ((-29) + z * ((-2) + z * ((-22) + z * ((-32) + z * ((-8) + z * ((-12) + z * ((-38) + z * ((-32) + z * ((-21) + z * ((-31) + z * ((-34) + z * ((-10) + z * ((-14) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_5 z * pow11_5 z = pow11_10_q z * f z + pow11_10 z + (41 : R) * pow11_10_mul_t z := by
  simp only [pow11_5, pow11_10_q, f, pow11_10, pow11_10_mul_t]
  
  ring

theorem pow11_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_5 z * pow11_5 z = pow11_10_q z * f z + pow11_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_10_mul_integer z


theorem pow11_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_5 z * pow11_5 z = pow11_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_10_mul z


theorem pow11_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 10 = pow11_10 z := by
  calc
    _ = u10 z ^ 5 * u10 z ^ 5 := by ring
    _ = pow11_5 z * pow11_5 z := by rw [pow11_5_pow z hz]
    _ = _ := pow11_10_root z hz


def pow11_20 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (6 + z * (37 + z * (18 + z * (28 + z * (32 + z * (21 + z * (36 + z * (39 + z * (29 + z * (36 + z * (12 + z * (7 + z * (13 + z * (34 + z * (32 + z * (25 + z * (29 + z * (23 + z * 34)))))))))))))))))))

def pow11_20_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (26 + z * (9 + z * (4 + z * (27 + z * (12 + z * (22 + z * (33 + z * (7 + z * (28 + z * (22 + z * (9 + z * (1 + z * (37 + z * (26 + z * (32 + z * (0 + z * (12 + z * 10))))))))))))))))))

def pow11_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-25) + z * ((-25) + z * ((-10) + z * ((-32) + z * ((-21) + z * ((-34) + z * ((-31) + z * ((-33) + z * ((-63) + z * ((-18) + z * ((-42) + z * ((-31) + z * ((-65) + z * ((-38) + z * ((-90) + z * ((-17) + z * ((-95) + z * ((-10) + z * (12 + z * ((-35) + z * ((-3) + z * (20 + z * ((-13) + z * ((-4) + z * ((-30) + z * ((-4) + z * (35 + z * ((-13) + z * (13 + z * (54 + z * (32 + z * (39 + z * (47 + z * (41 + z * (52 + z * (21 + z * (18 + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow11_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_10 z * pow11_10 z = pow11_20_q z * f z + pow11_20 z + (41 : R) * pow11_20_mul_t z := by
  simp only [pow11_10, pow11_20_q, f, pow11_20, pow11_20_mul_t]
  
  ring

theorem pow11_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_10 z * pow11_10 z = pow11_20_q z * f z + pow11_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_20_mul_integer z


theorem pow11_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_10 z * pow11_10 z = pow11_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_20_mul z


theorem pow11_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 20 = pow11_20 z := by
  calc
    _ = u10 z ^ 10 * u10 z ^ 10 := by ring
    _ = pow11_10 z * pow11_10 z := by rw [pow11_10_pow z hz]
    _ = _ := pow11_20_root z hz


def pow11_40 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (26 + z * (18 + z * (2 + z * (0 + z * (19 + z * (30 + z * (25 + z * (18 + z * (32 + z * (4 + z * (13 + z * (39 + z * (0 + z * (39 + z * (33 + z * (2 + z * (19 + z * (29 + z * 19)))))))))))))))))))

def pow11_40_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (40 + z * (9 + z * (18 + z * (23 + z * (34 + z * (39 + z * (22 + z * (34 + z * (27 + z * (13 + z * (17 + z * (39 + z * (31 + z * (9 + z * (19 + z * (37 + z * (12 + z * 8))))))))))))))))))

def pow11_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * ((-35) + z * (20 + z * ((-8) + z * (29 + z * (8 + z * (27 + z * (51 + z * (27 + z * (70 + z * (103 + z * (70 + z * (58 + z * (50 + z * (92 + z * (68 + z * (39 + z * (83 + z * (106 + z * (113 + z * (38 + z * (127 + z * (101 + z * (83 + z * (100 + z * (92 + z * (84 + z * (42 + z * (35 + z * (52 + z * (15 + z * (10 + z * (37 + z * (75 + z * (59 + z * (37 + z * (48 + z * (32 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow11_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_20 z * pow11_20 z = pow11_40_q z * f z + pow11_40 z + (41 : R) * pow11_40_mul_t z := by
  simp only [pow11_20, pow11_40_q, f, pow11_40, pow11_40_mul_t]
  
  ring

theorem pow11_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_20 z * pow11_20 z = pow11_40_q z * f z + pow11_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_40_mul_integer z


theorem pow11_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_20 z * pow11_20 z = pow11_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_40_mul z


theorem pow11_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 40 = pow11_40 z := by
  calc
    _ = u10 z ^ 20 * u10 z ^ 20 := by ring
    _ = pow11_20 z * pow11_20 z := by rw [pow11_20_pow z hz]
    _ = _ := pow11_40_root z hz


def pow11_41 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (7 + z * (1 + z * (10 + z * (0 + z * (39 + z * (15 + z * (38 + z * (3 + z * (36 + z * (16 + z * (14 + z * (19 + z * (23 + z * (6 + z * (39 + z * (22 + z * (28 + z * (38 + z * 7)))))))))))))))))))

def pow11_41_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (7 + z * (10 + z * (16 + z * (35 + z * (6 + z * (12 + z * (40 + z * (1 + z * (13 + z * (5 + z * (20 + z * (36 + z * (37 + z * (10 + z * (38 + z * (14 + z * (27 + z * 13))))))))))))))))))

def pow11_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * (9 + z * (0 + z * ((-4) + z * ((-33) + z * (16 + z * (5 + z * ((-9) + z * ((-1) + z * (22 + z * (22 + z * ((-38) + z * (5 + z * ((-24) + z * (13 + z * ((-45) + z * ((-32) + z * ((-51) + z * ((-44) + z * ((-35) + z * ((-42) + z * ((-42) + z * ((-51) + z * ((-52) + z * ((-48) + z * ((-33) + z * ((-55) + z * ((-52) + z * ((-64) + z * ((-71) + z * ((-77) + z * ((-67) + z * ((-52) + z * ((-40) + z * ((-48) + z * ((-17) + z * ((-11) + z * ((-2) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow11_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_40 z * u10 z = pow11_41_q z * f z + pow11_41 z + (41 : R) * pow11_41_mul_t z := by
  simp only [pow11_40, u10, pow11_41_q, f, pow11_41, pow11_41_mul_t]
  simp only [pow10_41]
  ring

theorem pow11_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_40 z * u10 z = pow11_41_q z * f z + pow11_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_41_mul_integer z


theorem pow11_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_40 z * u10 z = pow11_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_41_mul z


theorem pow11_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 41 = pow11_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow11_40_pow z hz]
  exact pow11_41_root z hz


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_41 z

theorem iterate11 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 11) = u11 z := by
  calc
    _ = (z ^ (41 ^ 10)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u10 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate10 z hz)
    _ = _ := pow11_41_pow z hz


def pow12_2 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (12 + z * (30 + z * (18 + z * (29 + z * (30 + z * (27 + z * (14 + z * (20 + z * (0 + z * (2 + z * (36 + z * (1 + z * (9 + z * (21 + z * (22 + z * (9 + z * (33 + z * (10 + z * 35)))))))))))))))))))

def pow12_2_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (23 + z * (28 + z * (29 + z * (26 + z * (28 + z * (23 + z * (13 + z * (27 + z * (10 + z * (31 + z * (39 + z * (17 + z * (25 + z * (3 + z * (29 + z * (33 + z * (5 + z * 8))))))))))))))))))

def pow12_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-24) + z * ((-58) + z * ((-40) + z * ((-80) + z * ((-30) + z * ((-41) + z * ((-44) + z * ((-71) + z * ((-43) + z * ((-42) + z * ((-92) + z * ((-33) + z * ((-77) + z * ((-19) + z * ((-84) + z * ((-39) + z * ((-87) + z * ((-20) + z * ((-94) + z * ((-37) + z * ((-24) + z * (24 + z * (13 + z * (46 + z * (35 + z * ((-11) + z * (5 + z * (23 + z * ((-9) + z * (13 + z * (17 + z * (12 + z * (60 + z * (29 + z * (28 + z * (37 + z * (7 + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow12_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z + (41 : R) * pow12_2_mul_t z := by
  simp only [u11, pow12_2_q, f, pow12_2, pow12_2_mul_t]
  simp only [pow11_41]
  ring

theorem pow12_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_2_mul_integer z


theorem pow12_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z * u11 z = pow12_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_2_mul z


theorem pow12_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 2 = pow12_2 z := by
  calc
    _ = u11 z ^ 1 * u11 z ^ 1 := by ring
    _ = u11 z * u11 z := by simp only [pow_one]
    _ = _ := pow12_2_root z hz


def pow12_4 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (40 + z * (1 + z * (1 + z * (24 + z * (39 + z * (18 + z * (20 + z * (23 + z * (23 + z * (22 + z * (1 + z * (31 + z * (19 + z * (0 + z * (37 + z * (2 + z * (9 + z * (19 + z * 32)))))))))))))))))))

def pow12_4_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (24 + z * (11 + z * (3 + z * (13 + z * (13 + z * (23 + z * (28 + z * (35 + z * (15 + z * (36 + z * (0 + z * (14 + z * (9 + z * (28 + z * (31 + z * (37 + z * (30 + z * 36))))))))))))))))))

def pow12_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-7) + z * (25 + z * (25 + z * (47 + z * (56 + z * (69 + z * (48 + z * (33 + z * (15 + z * (1 + z * (55 + z * ((-25) + z * (39 + z * ((-23) + z * ((-13) + z * ((-44) + z * ((-15) + z * ((-59) + z * (52 + z * ((-32) + z * (12 + z * ((-1) + z * ((-30) + z * ((-58) + z * ((-59) + z * ((-79) + z * ((-71) + z * ((-37) + z * ((-80) + z * ((-4) + z * ((-62) + z * ((-51) + z * ((-49) + z * ((-16) + z * ((-29) + z * (21 + z * ((-10) + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow12_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z + (41 : R) * pow12_4_mul_t z := by
  simp only [pow12_2, pow12_4_q, f, pow12_4, pow12_4_mul_t]
  
  ring

theorem pow12_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_4_mul_integer z


theorem pow12_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_2 z * pow12_2 z = pow12_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_4_mul z


theorem pow12_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 4 = pow12_4 z := by
  calc
    _ = u11 z ^ 2 * u11 z ^ 2 := by ring
    _ = pow12_2 z * pow12_2 z := by rw [pow12_2_pow z hz]
    _ = _ := pow12_4_root z hz


def pow12_5 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (2 + z * (22 + z * (11 + z * (33 + z * (30 + z * (16 + z * (33 + z * (18 + z * (6 + z * (33 + z * (35 + z * (33 + z * (22 + z * (23 + z * (21 + z * (11 + z * (18 + z * (12 + z * 15)))))))))))))))))))

def pow12_5_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (30 + z * (6 + z * (3 + z * (40 + z * (10 + z * (9 + z * (6 + z * (7 + z * (32 + z * (2 + z * (16 + z * (35 + z * (19 + z * (9 + z * (21 + z * (5 + z * (0 + z * 19))))))))))))))))))

def pow12_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (13 + z * (1 + z * ((-15) + z * ((-16) + z * ((-26) + z * (15 + z * (21 + z * (43 + z * ((-8) + z * (13 + z * (75 + z * ((-6) + z * (19 + z * (26 + z * (38 + z * (40 + z * (10 + z * (60 + z * (69 + z * (39 + z * (5 + z * (44 + z * (71 + z * (18 + z * (83 + z * (49 + z * (25 + z * (21 + z * (24 + z * ((-14) + z * (30 + z * (8 + z * (13 + z * (28 + z * (22 + z * (24 + z * (33 + z * (19 + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow12_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_4 z * u11 z = pow12_5_q z * f z + pow12_5 z + (41 : R) * pow12_5_mul_t z := by
  simp only [pow12_4, u11, pow12_5_q, f, pow12_5, pow12_5_mul_t]
  simp only [pow11_41]
  ring

theorem pow12_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_4 z * u11 z = pow12_5_q z * f z + pow12_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_5_mul_integer z


theorem pow12_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_4 z * u11 z = pow12_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_5_mul z


theorem pow12_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 5 = pow12_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow12_4_pow z hz]
  exact pow12_5_root z hz


def pow12_10 {R : Type*} [CommRing R] (z : R) : R := (12 + z * (13 + z * (37 + z * (18 + z * (11 + z * (31 + z * (22 + z * (20 + z * (7 + z * (16 + z * (24 + z * (22 + z * (25 + z * (32 + z * (9 + z * (24 + z * (0 + z * (27 + z * (8 + z * 2)))))))))))))))))))

def pow12_10_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (12 + z * (27 + z * (17 + z * (30 + z * (37 + z * (18 + z * (24 + z * (19 + z * (29 + z * (1 + z * (30 + z * (10 + z * (16 + z * (37 + z * (36 + z * (0 + z * (6 + z * 20))))))))))))))))))

def pow12_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-18) + z * ((-27) + z * ((-20) + z * ((-28) + z * ((-23) + z * ((-16) + z * ((-10) + z * ((-7) + z * ((-18) + z * (34 + z * ((-5) + z * (43 + z * (1 + z * (41 + z * (12 + z * (10 + z * (56 + z * (23 + z * (13 + z * (15 + z * (31 + z * (13 + z * (35 + z * (38 + z * (14 + z * (13 + z * (27 + z * (6 + z * (5 + z * ((-17) + z * ((-3) + z * ((-14) + z * ((-26) + z * ((-17) + z * (4 + z * (4 + z * ((-6) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow12_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_5 z * pow12_5 z = pow12_10_q z * f z + pow12_10 z + (41 : R) * pow12_10_mul_t z := by
  simp only [pow12_5, pow12_10_q, f, pow12_10, pow12_10_mul_t]
  
  ring

theorem pow12_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_5 z * pow12_5 z = pow12_10_q z * f z + pow12_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_10_mul_integer z


theorem pow12_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_5 z * pow12_5 z = pow12_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_10_mul z


theorem pow12_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 10 = pow12_10 z := by
  calc
    _ = u11 z ^ 5 * u11 z ^ 5 := by ring
    _ = pow12_5 z * pow12_5 z := by rw [pow12_5_pow z hz]
    _ = _ := pow12_10_root z hz


def pow12_20 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (22 + z * (36 + z * (34 + z * (39 + z * (33 + z * (0 + z * (24 + z * (28 + z * (33 + z * (12 + z * (3 + z * (18 + z * (4 + z * (26 + z * (5 + z * (1 + z * (0 + z * (24 + z * 38)))))))))))))))))))

def pow12_20_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (29 + z * (7 + z * (7 + z * (4 + z * (19 + z * (28 + z * (29 + z * (3 + z * (37 + z * (26 + z * (1 + z * (27 + z * (14 + z * (10 + z * (40 + z * (38 + z * (35 + z * 4))))))))))))))))))

def pow12_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-26) + z * ((-8) + z * (3 + z * (20 + z * (8 + z * (17 + z * (16 + z * (14 + z * ((-12) + z * (2 + z * (7 + z * (29 + z * (29 + z * (15 + z * (41 + z * ((-42) + z * ((-38) + z * (5 + z * ((-9) + z * ((-16) + z * ((-41) + z * ((-3) + z * ((-38) + z * ((-57) + z * ((-54) + z * ((-56) + z * ((-42) + z * ((-47) + z * ((-47) + z * ((-26) + z * ((-92) + z * ((-63) + z * ((-67) + z * ((-48) + z * ((-35) + z * ((-24) + z * ((-3) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow12_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_10 z * pow12_10 z = pow12_20_q z * f z + pow12_20 z + (41 : R) * pow12_20_mul_t z := by
  simp only [pow12_10, pow12_20_q, f, pow12_20, pow12_20_mul_t]
  
  ring

theorem pow12_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_10 z * pow12_10 z = pow12_20_q z * f z + pow12_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_20_mul_integer z


theorem pow12_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_10 z * pow12_10 z = pow12_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_20_mul z


theorem pow12_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 20 = pow12_20 z := by
  calc
    _ = u11 z ^ 10 * u11 z ^ 10 := by ring
    _ = pow12_10 z * pow12_10 z := by rw [pow12_10_pow z hz]
    _ = _ := pow12_20_root z hz


def pow12_40 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (14 + z * (10 + z * (15 + z * (29 + z * (23 + z * (1 + z * (40 + z * (36 + z * (3 + z * (13 + z * (30 + z * (11 + z * (35 + z * (15 + z * (3 + z * (14 + z * (40 + z * (20 + z * 7)))))))))))))))))))

def pow12_40_q {R : Type*} [CommRing R] (z : R) : R := (8 + z * (21 + z * (11 + z * (24 + z * (31 + z * (25 + z * (12 + z * (34 + z * (17 + z * (23 + z * (23 + z * (30 + z * (12 + z * (8 + z * (37 + z * (6 + z * (10 + z * (37 + z * 9))))))))))))))))))

def pow12_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-2) + z * (21 + z * (28 + z * (52 + z * (63 + z * (79 + z * (63 + z * (58 + z * (68 + z * (74 + z * (32 + z * (67 + z * (45 + z * (6 + z * ((-19) + z * ((-2) + z * ((-17) + z * ((-70) + z * ((-31) + z * ((-32) + z * ((-19) + z * ((-3) + z * (20 + z * ((-62) + z * ((-113) + z * ((-32) + z * ((-7) + z * ((-25) + z * ((-68) + z * ((-54) + z * ((-33) + z * ((-33) + z * ((-19) + z * ((-27) + z * ((-26) + z * ((-17) + z * (37 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow12_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_20 z * pow12_20 z = pow12_40_q z * f z + pow12_40 z + (41 : R) * pow12_40_mul_t z := by
  simp only [pow12_20, pow12_40_q, f, pow12_40, pow12_40_mul_t]
  
  ring

theorem pow12_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_20 z * pow12_20 z = pow12_40_q z * f z + pow12_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_40_mul_integer z


theorem pow12_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_20 z * pow12_20 z = pow12_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_40_mul z


theorem pow12_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 40 = pow12_40 z := by
  calc
    _ = u11 z ^ 20 * u11 z ^ 20 := by ring
    _ = pow12_20 z * pow12_20 z := by rw [pow12_20_pow z hz]
    _ = _ := pow12_40_root z hz


def pow12_41 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (14 + z * (10 + z * (18 + z * (38 + z * (35 + z * (4 + z * (22 + z * (4 + z * (37 + z * (23 + z * (29 + z * (12 + z * (14 + z * (17 + z * (26 + z * (12 + z * (36 + z * (5 + z * 25)))))))))))))))))))

def pow12_41_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (32 + z * (25 + z * (20 + z * (6 + z * (1 + z * (16 + z * (30 + z * (21 + z * (20 + z * (5 + z * (2 + z * (21 + z * (33 + z * (35 + z * (24 + z * (15 + z * (2 + z * 8))))))))))))))))))

def pow12_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-22) + z * ((-42) + z * ((-30) + z * ((-28) + z * (9 + z * ((-8) + z * (7 + z * ((-18) + z * ((-8) + z * (6 + z * ((-4) + z * (18 + z * (27 + z * ((-13) + z * ((-28) + z * ((-19) + z * (10 + z * (30 + z * (8 + z * (35 + z * (5 + z * (54 + z * (49 + z * (28 + z * (26 + z * (49 + z * (2 + z * (11 + z * (9 + z * ((-4) + z * ((-4) + z * (3 + z * (3 + z * (26 + z * (40 + z * (25 + z * (4 + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow12_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_40 z * u11 z = pow12_41_q z * f z + pow12_41 z + (41 : R) * pow12_41_mul_t z := by
  simp only [pow12_40, u11, pow12_41_q, f, pow12_41, pow12_41_mul_t]
  simp only [pow11_41]
  ring

theorem pow12_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_40 z * u11 z = pow12_41_q z * f z + pow12_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_41_mul_integer z


theorem pow12_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_40 z * u11 z = pow12_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_41_mul z


theorem pow12_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 41 = pow12_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow12_40_pow z hz]
  exact pow12_41_root z hz


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_41 z

theorem iterate12 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 12) = u12 z := by
  calc
    _ = (z ^ (41 ^ 11)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate11 z hz)
    _ = _ := pow12_41_pow z hz

end DimensionTen.Mod41

end

end OAI
