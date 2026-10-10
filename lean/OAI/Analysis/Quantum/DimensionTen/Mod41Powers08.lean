import OAI.Analysis.Quantum.DimensionTen.Mod41Powers07

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow15_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (29 + z * (4 + z * (21 + z * (5 + z * (39 + z * (39 + z * (10 + z * (33 + z * (7 + z * (19 + z * (29 + z * (19 + z * (35 + z * (16 + z * (10 + z * (21 + z * (35 + z * (16 + z * 35)))))))))))))))))))

def pow15_2_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (19 + z * (16 + z * (37 + z * (19 + z * (6 + z * (31 + z * (17 + z * (38 + z * (25 + z * (37 + z * (8 + z * (25 + z * (7 + z * (13 + z * (24 + z * (10 + z * (26 + z * 8))))))))))))))))))

def pow15_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (21 + z * (33 + z * ((-13) + z * (3 + z * (10 + z * (23 + z * (35 + z * ((-26) + z * (12 + z * ((-22) + z * ((-29) + z * ((-12) + z * (13 + z * ((-13) + z * ((-53) + z * ((-34) + z * ((-67) + z * ((-7) + z * ((-79) + z * ((-56) + z * ((-71) + z * ((-53) + z * ((-86) + z * ((-54) + z * ((-76) + z * ((-75) + z * ((-79) + z * ((-42) + z * ((-45) + z * ((-19) + z * ((-42) + z * ((-36) + z * ((-33) + z * ((-15) + z * ((-2) + z * ((-9) + z * (0 + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow15_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z + (41 : R) * pow15_2_mul_t z := by
  simp only [u14, pow15_2_q, f, pow15_2, pow15_2_mul_t]
  simp only [pow14_41]
  ring

theorem pow15_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_2_mul_integer z


theorem pow15_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z * u14 z = pow15_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_2_mul z


theorem pow15_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 2 = pow15_2 z := by
  calc
    _ = u14 z ^ 1 * u14 z ^ 1 := by ring
    _ = u14 z * u14 z := by simp only [pow_one]
    _ = _ := pow15_2_root z hz


def pow15_4 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (12 + z * (38 + z * (13 + z * (4 + z * (38 + z * (0 + z * (25 + z * (8 + z * (10 + z * (22 + z * (16 + z * (16 + z * (11 + z * (40 + z * (29 + z * (17 + z * (38 + z * (30 + z * 36)))))))))))))))))))

def pow15_4_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (2 + z * (2 + z * (15 + z * (5 + z * (27 + z * (21 + z * (30 + z * (35 + z * (34 + z * (16 + z * (33 + z * (35 + z * (29 + z * (38 + z * (10 + z * (33 + z * (40 + z * 36))))))))))))))))))

def pow15_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-3) + z * (15 + z * ((-10) + z * (17 + z * ((-28) + z * (34 + z * (0 + z * ((-3) + z * (9 + z * ((-13) + z * (37 + z * ((-1) + z * (3 + z * (21 + z * ((-22) + z * ((-4) + z * ((-4) + z * (2 + z * (19 + z * (5 + z * ((-13) + z * (17 + z * ((-4) + z * (6 + z * ((-13) + z * ((-52) + z * ((-23) + z * ((-65) + z * ((-24) + z * (9 + z * ((-30) + z * ((-27) + z * ((-44) + z * ((-10) + z * (2 + z * (21 + z * (0 + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (41 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

theorem pow15_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_4_mul_integer z


theorem pow15_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_2 z * pow15_2 z = pow15_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_4_mul z


theorem pow15_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 4 = pow15_4 z := by
  calc
    _ = u14 z ^ 2 * u14 z ^ 2 := by ring
    _ = pow15_2 z * pow15_2 z := by rw [pow15_2_pow z hz]
    _ = _ := pow15_4_root z hz


def pow15_5 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (0 + z * (32 + z * (13 + z * (32 + z * (15 + z * (33 + z * (9 + z * (26 + z * (20 + z * (5 + z * (29 + z * (3 + z * (4 + z * (9 + z * (26 + z * (13 + z * (29 + z * (20 + z * 2)))))))))))))))))))

def pow15_5_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (32 + z * (35 + z * (10 + z * (33 + z * (14 + z * (14 + z * (38 + z * (2 + z * (2 + z * (35 + z * (3 + z * (8 + z * (20 + z * (34 + z * (30 + z * (31 + z * (17 + z * 6))))))))))))))))))

def pow15_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-13) + z * ((-18) + z * (7 + z * ((-32) + z * ((-12) + z * (8 + z * ((-17) + z * (0 + z * ((-22) + z * ((-14) + z * (2 + z * ((-34) + z * (10 + z * ((-38) + z * ((-19) + z * ((-46) + z * ((-55) + z * ((-27) + z * (10 + z * (13 + z * ((-37) + z * ((-21) + z * (19 + z * ((-14) + z * ((-16) + z * ((-18) + z * (17 + z * ((-10) + z * ((-33) + z * ((-13) + z * ((-12) + z * ((-30) + z * ((-21) + z * ((-4) + z * (18 + z * (17 + z * (17 + z * 6))))))))))))))))))))))))))))))))))))))

theorem pow15_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_4 z * u14 z = pow15_5_q z * f z + pow15_5 z + (41 : R) * pow15_5_mul_t z := by
  simp only [pow15_4, u14, pow15_5_q, f, pow15_5, pow15_5_mul_t]
  simp only [pow14_41]
  ring

theorem pow15_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_4 z * u14 z = pow15_5_q z * f z + pow15_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_5_mul_integer z


theorem pow15_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_4 z * u14 z = pow15_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_5_mul z


theorem pow15_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 5 = pow15_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow15_4_pow z hz]
  exact pow15_5_root z hz


def pow15_10 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (19 + z * (12 + z * (4 + z * (13 + z * (12 + z * (1 + z * (30 + z * (33 + z * (27 + z * (26 + z * (22 + z * (22 + z * (6 + z * (40 + z * (14 + z * (28 + z * (4 + z * (8 + z * 31)))))))))))))))))))

def pow15_10_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (17 + z * (35 + z * (17 + z * (37 + z * (37 + z * (36 + z * (30 + z * (12 + z * (0 + z * (21 + z * (4 + z * (39 + z * (36 + z * (7 + z * (2 + z * (8 + z * (1 + z * 4))))))))))))))))))

def pow15_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-23) + z * ((-29) + z * ((-29) + z * ((-33) + z * ((-42) + z * ((-21) + z * ((-53) + z * (1 + z * ((-30) + z * (1 + z * ((-3) + z * ((-55) + z * ((-33) + z * ((-75) + z * ((-35) + z * ((-86) + z * ((-32) + z * ((-62) + z * ((-32) + z * ((-59) + z * ((-57) + z * ((-32) + z * ((-38) + z * ((-35) + z * ((-17) + z * (9 + z * ((-37) + z * ((-27) + z * ((-33) + z * ((-20) + z * ((-24) + z * (9 + z * (29 + z * (27 + z * (21 + z * (10 + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow15_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_5 z * pow15_5 z = pow15_10_q z * f z + pow15_10 z + (41 : R) * pow15_10_mul_t z := by
  simp only [pow15_5, pow15_10_q, f, pow15_10, pow15_10_mul_t]
  
  ring

theorem pow15_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_5 z * pow15_5 z = pow15_10_q z * f z + pow15_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_10_mul_integer z


theorem pow15_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_5 z * pow15_5 z = pow15_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_10_mul z


theorem pow15_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 10 = pow15_10 z := by
  calc
    _ = u14 z ^ 5 * u14 z ^ 5 := by ring
    _ = pow15_5 z * pow15_5 z := by rw [pow15_5_pow z hz]
    _ = _ := pow15_10_root z hz


def pow15_20 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (20 + z * (12 + z * (12 + z * (5 + z * (13 + z * (2 + z * (27 + z * (23 + z * (35 + z * (11 + z * (21 + z * (12 + z * (40 + z * (24 + z * (16 + z * (3 + z * (34 + z * (5 + z * 15)))))))))))))))))))

def pow15_20_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (27 + z * (31 + z * (16 + z * (15 + z * (24 + z * (5 + z * (40 + z * (6 + z * (10 + z * (20 + z * (6 + z * (36 + z * (22 + z * (30 + z * (33 + z * (14 + z * (38 + z * 18))))))))))))))))))

def pow15_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-25) + z * ((-40) + z * ((-32) + z * ((-48) + z * ((-44) + z * ((-32) + z * ((-70) + z * ((-24) + z * ((-41) + z * ((-14) + z * ((-34) + z * ((-42) + z * ((-30) + z * ((-73) + z * ((-28) + z * ((-44) + z * ((-66) + z * ((-47) + z * ((-50) + z * ((-17) + z * ((-21) + z * ((-20) + z * (25 + z * (1 + z * ((-15) + z * (14 + z * (6 + z * ((-3) + z * ((-43) + z * ((-4) + z * ((-55) + z * ((-57) + z * ((-19) + z * ((-34) + z * (7 + z * ((-28) + z * ((-2) + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow15_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_10 z * pow15_10 z = pow15_20_q z * f z + pow15_20 z + (41 : R) * pow15_20_mul_t z := by
  simp only [pow15_10, pow15_20_q, f, pow15_20, pow15_20_mul_t]
  
  ring

theorem pow15_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_10 z * pow15_10 z = pow15_20_q z * f z + pow15_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_20_mul_integer z


theorem pow15_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_10 z * pow15_10 z = pow15_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_20_mul z


theorem pow15_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 20 = pow15_20 z := by
  calc
    _ = u14 z ^ 10 * u14 z ^ 10 := by ring
    _ = pow15_10 z * pow15_10 z := by rw [pow15_10_pow z hz]
    _ = _ := pow15_20_root z hz


def pow15_40 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (21 + z * (30 + z * (35 + z * (11 + z * (4 + z * (10 + z * (32 + z * (18 + z * (11 + z * (26 + z * (19 + z * (39 + z * (1 + z * (10 + z * (21 + z * (38 + z * (38 + z * (23 + z * 19)))))))))))))))))))

def pow15_40_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (35 + z * (25 + z * (25 + z * (15 + z * (0 + z * (7 + z * (3 + z * (38 + z * (39 + z * (40 + z * (36 + z * (27 + z * (17 + z * (23 + z * (39 + z * (19 + z * (1 + z * 20))))))))))))))))))

def pow15_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-36) + z * ((-35) + z * ((-45) + z * ((-37) + z * ((-41) + z * ((-23) + z * ((-29) + z * ((-55) + z * ((-50) + z * ((-61) + z * ((-80) + z * ((-81) + z * ((-82) + z * ((-34) + z * ((-82) + z * ((-65) + z * ((-99) + z * ((-62) + z * ((-102) + z * ((-40) + z * ((-16) + z * ((-12) + z * ((-57) + z * ((-9) + z * ((-72) + z * ((-23) + z * ((-64) + z * ((-28) + z * ((-79) + z * ((-25) + z * ((-32) + z * ((-11) + z * ((-36) + z * ((-13) + z * ((-16) + z * (16 + z * ((-11) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow15_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_20 z * pow15_20 z = pow15_40_q z * f z + pow15_40 z + (41 : R) * pow15_40_mul_t z := by
  simp only [pow15_20, pow15_40_q, f, pow15_40, pow15_40_mul_t]
  
  ring

theorem pow15_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_20 z * pow15_20 z = pow15_40_q z * f z + pow15_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_40_mul_integer z


theorem pow15_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_20 z * pow15_20 z = pow15_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_40_mul z


theorem pow15_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 40 = pow15_40 z := by
  calc
    _ = u14 z ^ 20 * u14 z ^ 20 := by ring
    _ = pow15_20 z * pow15_20 z := by rw [pow15_20_pow z hz]
    _ = _ := pow15_40_root z hz


def pow15_41 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (4 + z * (4 + z * (17 + z * (24 + z * (11 + z * (4 + z * (5 + z * (16 + z * (11 + z * (17 + z * (15 + z * (8 + z * (33 + z * (15 + z * (16 + z * (22 + z * (23 + z * (29 + z * 28)))))))))))))))))))

def pow15_41_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (25 + z * (26 + z * (6 + z * (11 + z * (5 + z * (36 + z * (30 + z * (32 + z * (32 + z * (15 + z * (6 + z * (38 + z * (32 + z * (3 + z * (39 + z * (2 + z * (17 + z * 10))))))))))))))))))

def pow15_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * (9 + z * ((-11) + z * (28 + z * (13 + z * (17 + z * (11 + z * ((-2) + z * ((-5) + z * ((-6) + z * ((-25) + z * ((-12) + z * (10 + z * ((-3) + z * ((-37) + z * ((-58) + z * ((-18) + z * ((-64) + z * (35 + z * ((-34) + z * (0 + z * ((-17) + z * ((-36) + z * ((-43) + z * ((-33) + z * ((-39) + z * ((-53) + z * ((-42) + z * ((-17) + z * ((-19) + z * ((-16) + z * ((-35) + z * ((-24) + z * (7 + z * (2 + z * (28 + z * (7 + z * (5 + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow15_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_40 z * u14 z = pow15_41_q z * f z + pow15_41 z + (41 : R) * pow15_41_mul_t z := by
  simp only [pow15_40, u14, pow15_41_q, f, pow15_41, pow15_41_mul_t]
  simp only [pow14_41]
  ring

theorem pow15_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_40 z * u14 z = pow15_41_q z * f z + pow15_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_41_mul_integer z


theorem pow15_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_40 z * u14 z = pow15_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_41_mul z


theorem pow15_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 41 = pow15_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow15_40_pow z hz]
  exact pow15_41_root z hz


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_41 z

theorem iterate15 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 15) = u15 z := by
  calc
    _ = (z ^ (41 ^ 14)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u14 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate14 z hz)
    _ = _ := pow15_41_pow z hz


def pow16_2 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (28 + z * (17 + z * (10 + z * (19 + z * (8 + z * (28 + z * (34 + z * (36 + z * (30 + z * (3 + z * (38 + z * (37 + z * (16 + z * (39 + z * (11 + z * (11 + z * (23 + z * (38 + z * 8)))))))))))))))))))

def pow16_2_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (20 + z * (22 + z * (6 + z * (20 + z * (32 + z * (40 + z * (40 + z * (9 + z * (0 + z * (29 + z * (23 + z * (14 + z * (13 + z * (27 + z * (4 + z * (13 + z * (39 + z * 5))))))))))))))))))

def pow16_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-19) + z * ((-31) + z * ((-15) + z * ((-25) + z * ((-41) + z * ((-64) + z * ((-63) + z * ((-54) + z * ((-64) + z * ((-65) + z * ((-71) + z * ((-76) + z * ((-53) + z * ((-92) + z * ((-76) + z * ((-71) + z * ((-91) + z * ((-88) + z * ((-62) + z * ((-59) + z * ((-94) + z * ((-46) + z * ((-28) + z * ((-65) + z * ((-67) + z * ((-14) + z * (9 + z * ((-5) + z * (6 + z * (19 + z * (21 + z * (25 + z * (3 + z * (31 + z * (34 + z * (21 + z * (35 + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow16_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z + (41 : R) * pow16_2_mul_t z := by
  simp only [u15, pow16_2_q, f, pow16_2, pow16_2_mul_t]
  simp only [pow15_41]
  ring

theorem pow16_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_2_mul_integer z


theorem pow16_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z * u15 z = pow16_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_2_mul z


theorem pow16_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 2 = pow16_2 z := by
  calc
    _ = u15 z ^ 1 * u15 z ^ 1 := by ring
    _ = u15 z * u15 z := by simp only [pow_one]
    _ = _ := pow16_2_root z hz


def pow16_4 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (22 + z * (25 + z * (9 + z * (39 + z * (20 + z * (35 + z * (18 + z * (37 + z * (2 + z * (27 + z * (33 + z * (37 + z * (25 + z * (5 + z * (32 + z * (28 + z * (19 + z * (8 + z * 3)))))))))))))))))))

def pow16_4_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (36 + z * (33 + z * (11 + z * (11 + z * (5 + z * (24 + z * (10 + z * (15 + z * (19 + z * (9 + z * (33 + z * (28 + z * (7 + z * (34 + z * (11 + z * (27 + z * (0 + z * 23))))))))))))))))))

def pow16_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-38) + z * ((-47) + z * ((-22) + z * ((-45) + z * ((-14) + z * ((-27) + z * ((-4) + z * ((-3) + z * (16 + z * (21 + z * ((-26) + z * (22 + z * (46 + z * (34 + z * (70 + z * ((-14) + z * (27 + z * (32 + z * (86 + z * (101 + z * (81 + z * (73 + z * (87 + z * (94 + z * (97 + z * (92 + z * (28 + z * (20 + z * (42 + z * (24 + z * (14 + z * (32 + z * ((-17) + z * ((-1) + z * (14 + z * (34 + z * ((-2) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow16_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z + (41 : R) * pow16_4_mul_t z := by
  simp only [pow16_2, pow16_4_q, f, pow16_4, pow16_4_mul_t]
  
  ring

theorem pow16_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_4_mul_integer z


theorem pow16_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_2 z * pow16_2 z = pow16_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_4_mul z


theorem pow16_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 4 = pow16_4 z := by
  calc
    _ = u15 z ^ 2 * u15 z ^ 2 := by ring
    _ = pow16_2 z * pow16_2 z := by rw [pow16_2_pow z hz]
    _ = _ := pow16_4_root z hz


def pow16_5 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (35 + z * (34 + z * (29 + z * (2 + z * (4 + z * (27 + z * (0 + z * (4 + z * (2 + z * (16 + z * (16 + z * (20 + z * (40 + z * (3 + z * (9 + z * (26 + z * (36 + z * (38 + z * 18)))))))))))))))))))

def pow16_5_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (17 + z * (7 + z * (36 + z * (39 + z * (0 + z * (30 + z * (31 + z * (23 + z * (20 + z * (17 + z * (36 + z * (20 + z * (6 + z * (29 + z * (24 + z * (34 + z * (5 + z * 2))))))))))))))))))

def pow16_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-19) + z * ((-29) + z * ((-32) + z * ((-45) + z * ((-17) + z * ((-21) + z * ((-55) + z * ((-56) + z * ((-18) + z * ((-40) + z * ((-85) + z * ((-31) + z * ((-29) + z * ((-58) + z * ((-59) + z * ((-56) + z * ((-29) + z * ((-74) + z * ((-31) + z * ((-3) + z * (11 + z * ((-45) + z * ((-23) + z * (15 + z * ((-3) + z * ((-12) + z * ((-12) + z * (11 + z * (27 + z * (1 + z * (1 + z * (3 + z * (0 + z * (21 + z * (10 + z * (15 + z * (6 + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow16_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_4 z * u15 z = pow16_5_q z * f z + pow16_5 z + (41 : R) * pow16_5_mul_t z := by
  simp only [pow16_4, u15, pow16_5_q, f, pow16_5, pow16_5_mul_t]
  simp only [pow15_41]
  ring

theorem pow16_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_4 z * u15 z = pow16_5_q z * f z + pow16_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_5_mul_integer z


theorem pow16_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_4 z * u15 z = pow16_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_5_mul z


theorem pow16_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 5 = pow16_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow16_4_pow z hz]
  exact pow16_5_root z hz


def pow16_10 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (33 + z * (12 + z * (9 + z * (36 + z * (1 + z * (39 + z * (2 + z * (16 + z * (39 + z * (8 + z * (24 + z * (2 + z * (19 + z * (29 + z * (0 + z * (37 + z * (26 + z * (8 + z * 19)))))))))))))))))))

def pow16_10_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (24 + z * (36 + z * (26 + z * (17 + z * (1 + z * (21 + z * (26 + z * (20 + z * (27 + z * (32 + z * (8 + z * (40 + z * (35 + z * (36 + z * (25 + z * (29 + z * (12 + z * 37))))))))))))))))))

def pow16_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (27 + z * (37 + z * (47 + z * (28 + z * (12 + z * (5 + z * ((-2) + z * ((-23) + z * ((-47) + z * ((-79) + z * ((-43) + z * ((-26) + z * ((-1) + z * ((-41) + z * ((-30) + z * ((-56) + z * ((-69) + z * ((-23) + z * (49 + z * ((-57) + z * ((-67) + z * ((-97) + z * ((-76) + z * ((-67) + z * ((-109) + z * ((-89) + z * ((-88) + z * ((-57) + z * ((-31) + z * (1 + z * ((-15) + z * ((-39) + z * ((-31) + z * (20 + z * (42 + z * (42 + z * (6 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow16_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_5 z * pow16_5 z = pow16_10_q z * f z + pow16_10 z + (41 : R) * pow16_10_mul_t z := by
  simp only [pow16_5, pow16_10_q, f, pow16_10, pow16_10_mul_t]
  
  ring

theorem pow16_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_5 z * pow16_5 z = pow16_10_q z * f z + pow16_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_10_mul_integer z


theorem pow16_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_5 z * pow16_5 z = pow16_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_10_mul z


theorem pow16_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 10 = pow16_10 z := by
  calc
    _ = u15 z ^ 5 * u15 z ^ 5 := by ring
    _ = pow16_5 z * pow16_5 z := by rw [pow16_5_pow z hz]
    _ = _ := pow16_10_root z hz


def pow16_20 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (26 + z * (9 + z * (32 + z * (10 + z * (19 + z * (2 + z * (37 + z * (33 + z * (19 + z * (3 + z * (1 + z * (0 + z * (27 + z * (35 + z * (5 + z * (39 + z * (15 + z * (2 + z * 4)))))))))))))))))))

def pow16_20_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (34 + z * (38 + z * (30 + z * (25 + z * (12 + z * (24 + z * (21 + z * (25 + z * (29 + z * (10 + z * (23 + z * (33 + z * (34 + z * (25 + z * (23 + z * (38 + z * (11 + z * 33))))))))))))))))))

def pow16_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * (8 + z * ((-26) + z * ((-32) + z * ((-16) + z * ((-8) + z * (5 + z * ((-12) + z * ((-34) + z * ((-15) + z * (31 + z * ((-65) + z * ((-20) + z * ((-51) + z * ((-42) + z * ((-26) + z * ((-133) + z * ((-11) + z * ((-81) + z * ((-93) + z * ((-31) + z * ((-96) + z * ((-31) + z * ((-42) + z * ((-86) + z * ((-10) + z * ((-72) + z * ((-48) + z * ((-54) + z * ((-81) + z * ((-27) + z * ((-71) + z * ((-47) + z * ((-14) + z * ((-35) + z * ((-7) + z * (3 + z * ((-17) + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow16_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_10 z * pow16_10 z = pow16_20_q z * f z + pow16_20 z + (41 : R) * pow16_20_mul_t z := by
  simp only [pow16_10, pow16_20_q, f, pow16_20, pow16_20_mul_t]
  
  ring

theorem pow16_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_10 z * pow16_10 z = pow16_20_q z * f z + pow16_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_20_mul_integer z


theorem pow16_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_10 z * pow16_10 z = pow16_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_20_mul z


theorem pow16_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 20 = pow16_20 z := by
  calc
    _ = u15 z ^ 10 * u15 z ^ 10 := by ring
    _ = pow16_10 z * pow16_10 z := by rw [pow16_10_pow z hz]
    _ = _ := pow16_20_root z hz


def pow16_40 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (25 + z * (14 + z * (16 + z * (17 + z * (18 + z * (23 + z * (13 + z * (1 + z * (13 + z * (11 + z * (6 + z * (35 + z * (22 + z * (29 + z * (37 + z * (0 + z * (26 + z * (1 + z * 8)))))))))))))))))))

def pow16_40_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (40 + z * (25 + z * (37 + z * (29 + z * (3 + z * (30 + z * (12 + z * (12 + z * (5 + z * (2 + z * (18 + z * (30 + z * (16 + z * (37 + z * (17 + z * (37 + z * (28 + z * 16))))))))))))))))))

def pow16_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (13 + z * (2 + z * ((-16) + z * ((-6) + z * ((-11) + z * ((-15) + z * ((-18) + z * (18 + z * (30 + z * (33 + z * (15 + z * ((-24) + z * ((-35) + z * ((-32) + z * ((-3) + z * ((-28) + z * ((-7) + z * ((-13) + z * ((-118) + z * ((-80) + z * ((-86) + z * ((-16) + z * ((-47) + z * ((-29) + z * ((-17) + z * ((-65) + z * ((-62) + z * ((-59) + z * ((-77) + z * ((-49) + z * ((-25) + z * ((-78) + z * ((-52) + z * ((-56) + z * ((-47) + z * ((-39) + z * ((-25) + z * ((-12) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow16_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_20 z * pow16_20 z = pow16_40_q z * f z + pow16_40 z + (41 : R) * pow16_40_mul_t z := by
  simp only [pow16_20, pow16_40_q, f, pow16_40, pow16_40_mul_t]
  
  ring

theorem pow16_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_20 z * pow16_20 z = pow16_40_q z * f z + pow16_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_40_mul_integer z


theorem pow16_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_20 z * pow16_20 z = pow16_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_40_mul z


theorem pow16_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 40 = pow16_40 z := by
  calc
    _ = u15 z ^ 20 * u15 z ^ 20 := by ring
    _ = pow16_20 z * pow16_20 z := by rw [pow16_20_pow z hz]
    _ = _ := pow16_40_root z hz


def pow16_41 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (22 + z * (16 + z * (31 + z * (12 + z * (28 + z * (39 + z * (39 + z * (25 + z * (11 + z * (6 + z * (28 + z * (12 + z * (1 + z * (9 + z * (7 + z * (28 + z * (3 + z * (36 + z * 13)))))))))))))))))))

def pow16_41_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (14 + z * (28 + z * (40 + z * (23 + z * (2 + z * (32 + z * (17 + z * (21 + z * (21 + z * (35 + z * (20 + z * (12 + z * (40 + z * (13 + z * (2 + z * (37 + z * (18 + z * 19))))))))))))))))))

def pow16_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-14) + z * ((-46) + z * ((-42) + z * ((-55) + z * ((-22) + z * ((-38) + z * ((-58) + z * ((-65) + z * ((-36) + z * ((-92) + z * ((-92) + z * ((-63) + z * ((-88) + z * ((-82) + z * ((-72) + z * ((-76) + z * ((-105) + z * ((-111) + z * ((-60) + z * ((-88) + z * ((-82) + z * ((-53) + z * ((-44) + z * ((-65) + z * ((-54) + z * ((-44) + z * ((-52) + z * ((-28) + z * ((-36) + z * (8 + z * (6 + z * ((-20) + z * (0 + z * (1 + z * ((-22) + z * (1 + z * ((-8) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow16_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_40 z * u15 z = pow16_41_q z * f z + pow16_41 z + (41 : R) * pow16_41_mul_t z := by
  simp only [pow16_40, u15, pow16_41_q, f, pow16_41, pow16_41_mul_t]
  simp only [pow15_41]
  ring

theorem pow16_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_40 z * u15 z = pow16_41_q z * f z + pow16_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_41_mul_integer z


theorem pow16_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_40 z * u15 z = pow16_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_41_mul z


theorem pow16_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 41 = pow16_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow16_40_pow z hz]
  exact pow16_41_root z hz


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_41 z

theorem iterate16 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 16) = u16 z := by
  calc
    _ = (z ^ (41 ^ 15)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u15 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate15 z hz)
    _ = _ := pow16_41_pow z hz

end DimensionTen.Mod41

end

end OAI
