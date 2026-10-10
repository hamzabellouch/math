import OAI.Analysis.Quantum.DimensionTen.Mod41Powers08

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow17_2 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (34 + z * (10 + z * (7 + z * (17 + z * (21 + z * (5 + z * (36 + z * (23 + z * (26 + z * (33 + z * (12 + z * (17 + z * (10 + z * (23 + z * (16 + z * (8 + z * (18 + z * (39 + z * 20)))))))))))))))))))

def pow17_2_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (10 + z * (11 + z * (14 + z * (27 + z * (25 + z * (21 + z * (24 + z * (25 + z * (28 + z * (14 + z * (32 + z * (0 + z * (35 + z * (14 + z * (33 + z * (13 + z * (7 + z * 5))))))))))))))))))

def pow17_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * (19 + z * (2 + z * (49 + z * ((-3) + z * (34 + z * (76 + z * (64 + z * (69 + z * (55 + z * (50 + z * (42 + z * (73 + z * (21 + z * (49 + z * ((-63) + z * ((-1) + z * ((-29) + z * (24 + z * (3 + z * ((-49) + z * ((-4) + z * ((-25) + z * ((-12) + z * ((-15) + z * ((-13) + z * ((-35) + z * ((-34) + z * ((-61) + z * ((-34) + z * ((-42) + z * ((-46) + z * ((-33) + z * ((-20) + z * (16 + z * (7 + z * (26 + z * (19 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow17_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z + (41 : R) * pow17_2_mul_t z := by
  simp only [u16, pow17_2_q, f, pow17_2, pow17_2_mul_t]
  simp only [pow16_41]
  ring

theorem pow17_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_2_mul_integer z


theorem pow17_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z * u16 z = pow17_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_2_mul z


theorem pow17_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 2 = pow17_2 z := by
  calc
    _ = u16 z ^ 1 * u16 z ^ 1 := by ring
    _ = u16 z * u16 z := by simp only [pow_one]
    _ = _ := pow17_2_root z hz


def pow17_4 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (14 + z * (13 + z * (0 + z * (33 + z * (19 + z * (6 + z * (35 + z * (30 + z * (6 + z * (5 + z * (9 + z * (4 + z * (35 + z * (12 + z * (21 + z * (20 + z * (34 + z * (17 + z * 40)))))))))))))))))))

def pow17_4_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (30 + z * (17 + z * (36 + z * (35 + z * (6 + z * (28 + z * (27 + z * (5 + z * (38 + z * (25 + z * (36 + z * (18 + z * (34 + z * (18 + z * (23 + z * (34 + z * (15 + z * 31))))))))))))))))))

def pow17_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * (7 + z * ((-9) + z * ((-34) + z * ((-47) + z * ((-12) + z * ((-20) + z * ((-26) + z * ((-1) + z * (6 + z * (5 + z * ((-54) + z * ((-3) + z * ((-59) + z * ((-24) + z * ((-41) + z * ((-64) + z * ((-63) + z * ((-60) + z * (2 + z * ((-78) + z * ((-50) + z * ((-49) + z * ((-36) + z * ((-24) + z * ((-36) + z * ((-22) + z * ((-20) + z * ((-26) + z * ((-44) + z * ((-54) + z * ((-39) + z * ((-36) + z * ((-22) + z * ((-26) + z * ((-7) + z * (30 + z * (15 + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow17_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z + (41 : R) * pow17_4_mul_t z := by
  simp only [pow17_2, pow17_4_q, f, pow17_4, pow17_4_mul_t]
  
  ring

theorem pow17_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_4_mul_integer z


theorem pow17_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_2 z * pow17_2 z = pow17_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_4_mul z


theorem pow17_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 4 = pow17_4 z := by
  calc
    _ = u16 z ^ 2 * u16 z ^ 2 := by ring
    _ = pow17_2 z * pow17_2 z := by rw [pow17_2_pow z hz]
    _ = _ := pow17_4_root z hz


def pow17_5 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (30 + z * (32 + z * (6 + z * (32 + z * (10 + z * (0 + z * (16 + z * (28 + z * (24 + z * (13 + z * (19 + z * (24 + z * (2 + z * (25 + z * (6 + z * (40 + z * (10 + z * (9 + z * 14)))))))))))))))))))

def pow17_5_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (22 + z * (9 + z * (30 + z * (31 + z * (15 + z * (38 + z * (7 + z * (8 + z * (39 + z * (17 + z * (20 + z * (1 + z * (3 + z * (19 + z * (35 + z * (12 + z * (1 + z * 28))))))))))))))))))

def pow17_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-13) + z * ((-11) + z * ((-32) + z * ((-15) + z * ((-15) + z * ((-28) + z * (19 + z * (5 + z * (6 + z * ((-4) + z * ((-22) + z * (12 + z * (11 + z * (4 + z * ((-16) + z * ((-24) + z * ((-42) + z * ((-31) + z * (13 + z * (0 + z * ((-1) + z * ((-4) + z * (25 + z * (45 + z * ((-5) + z * (8 + z * (1 + z * ((-22) + z * ((-18) + z * ((-22) + z * (13 + z * ((-10) + z * ((-2) + z * ((-9) + z * (39 + z * (16 + z * (20 + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow17_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_4 z * u16 z = pow17_5_q z * f z + pow17_5 z + (41 : R) * pow17_5_mul_t z := by
  simp only [pow17_4, u16, pow17_5_q, f, pow17_5, pow17_5_mul_t]
  simp only [pow16_41]
  ring

theorem pow17_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_4 z * u16 z = pow17_5_q z * f z + pow17_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_5_mul_integer z


theorem pow17_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_4 z * u16 z = pow17_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_5_mul z


theorem pow17_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 5 = pow17_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow17_4_pow z hz]
  exact pow17_5_root z hz


def pow17_10 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (29 + z * (11 + z * (13 + z * (8 + z * (20 + z * (35 + z * (34 + z * (28 + z * (34 + z * (23 + z * (0 + z * (3 + z * (22 + z * (24 + z * (28 + z * (2 + z * (5 + z * (33 + z * 7)))))))))))))))))))

def pow17_10_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (21 + z * (11 + z * (2 + z * (13 + z * (22 + z * (3 + z * (13 + z * (34 + z * (18 + z * (11 + z * (1 + z * (12 + z * (13 + z * (36 + z * (31 + z * (24 + z * (30 + z * 32))))))))))))))))))

def pow17_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * ((-1) + z * (20 + z * (30 + z * (27 + z * (20 + z * (34 + z * ((-6) + z * (1 + z * (21 + z * (32 + z * (43 + z * (28 + z * (51 + z * (7 + z * ((-21) + z * (3 + z * ((-7) + z * (12 + z * ((-30) + z * (15 + z * ((-10) + z * ((-53) + z * ((-18) + z * ((-39) + z * ((-47) + z * ((-26) + z * ((-30) + z * ((-16) + z * ((-75) + z * ((-26) + z * ((-63) + z * ((-53) + z * ((-66) + z * ((-52) + z * ((-17) + z * ((-27) + z * ((-18) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow17_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_5 z * pow17_5 z = pow17_10_q z * f z + pow17_10 z + (41 : R) * pow17_10_mul_t z := by
  simp only [pow17_5, pow17_10_q, f, pow17_10, pow17_10_mul_t]
  
  ring

theorem pow17_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_5 z * pow17_5 z = pow17_10_q z * f z + pow17_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_10_mul_integer z


theorem pow17_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_5 z * pow17_5 z = pow17_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_10_mul z


theorem pow17_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 10 = pow17_10 z := by
  calc
    _ = u16 z ^ 5 * u16 z ^ 5 := by ring
    _ = pow17_5 z * pow17_5 z := by rw [pow17_5_pow z hz]
    _ = _ := pow17_10_root z hz


def pow17_20 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (8 + z * (21 + z * (21 + z * (16 + z * (20 + z * (35 + z * (9 + z * (20 + z * (13 + z * (27 + z * (31 + z * (4 + z * (13 + z * (12 + z * (25 + z * (14 + z * (24 + z * (35 + z * 37)))))))))))))))))))

def pow17_20_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (20 + z * (39 + z * (9 + z * (23 + z * (8 + z * (32 + z * (33 + z * (15 + z * (29 + z * (9 + z * (0 + z * (17 + z * (12 + z * (34 + z * (34 + z * (21 + z * (17 + z * 8))))))))))))))))))

def pow17_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (26 + z * ((-26) + z * (4 + z * ((-44) + z * (14 + z * (21 + z * (43 + z * (33 + z * (37 + z * (51 + z * ((-7) + z * (13 + z * (36 + z * (41 + z * (65 + z * ((-19) + z * ((-65) + z * ((-8) + z * ((-12) + z * ((-10) + z * ((-23) + z * ((-11) + z * ((-9) + z * (6 + z * ((-31) + z * ((-38) + z * (7 + z * ((-6) + z * ((-49) + z * ((-58) + z * ((-49) + z * ((-26) + z * ((-18) + z * ((-37) + z * ((-19) + z * (12 + z * (5 + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow17_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_10 z * pow17_10 z = pow17_20_q z * f z + pow17_20 z + (41 : R) * pow17_20_mul_t z := by
  simp only [pow17_10, pow17_20_q, f, pow17_20, pow17_20_mul_t]
  
  ring

theorem pow17_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_10 z * pow17_10 z = pow17_20_q z * f z + pow17_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_20_mul_integer z


theorem pow17_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_10 z * pow17_10 z = pow17_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_20_mul z


theorem pow17_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 20 = pow17_20 z := by
  calc
    _ = u16 z ^ 10 * u16 z ^ 10 := by ring
    _ = pow17_10 z * pow17_10 z := by rw [pow17_10_pow z hz]
    _ = _ := pow17_20_root z hz


def pow17_40 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (5 + z * (29 + z * (12 + z * (21 + z * (37 + z * (7 + z * (31 + z * (14 + z * (32 + z * (28 + z * (26 + z * (28 + z * (24 + z * (30 + z * (35 + z * (19 + z * (36 + z * (37 + z * 23)))))))))))))))))))

def pow17_40_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (32 + z * (12 + z * (16 + z * (4 + z * (4 + z * (25 + z * (34 + z * (12 + z * (37 + z * (17 + z * (25 + z * (13 + z * (39 + z * (13 + z * (26 + z * (27 + z * (19 + z * 16))))))))))))))))))

def pow17_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * ((-22) + z * ((-3) + z * ((-13) + z * (12 + z * (4 + z * (29 + z * ((-1) + z * (12 + z * ((-12) + z * (12 + z * (1 + z * (24 + z * ((-20) + z * (3 + z * ((-20) + z * ((-13) + z * ((-37) + z * ((-24) + z * (40 + z * ((-7) + z * (57 + z * (10 + z * (10 + z * (8 + z * (1 + z * ((-20) + z * ((-9) + z * ((-7) + z * (17 + z * ((-3) + z * ((-32) + z * ((-19) + z * (15 + z * (29 + z * (29 + z * (52 + z * (51 + z * 33))))))))))))))))))))))))))))))))))))))

theorem pow17_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_20 z * pow17_20 z = pow17_40_q z * f z + pow17_40 z + (41 : R) * pow17_40_mul_t z := by
  simp only [pow17_20, pow17_40_q, f, pow17_40, pow17_40_mul_t]
  
  ring

theorem pow17_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_20 z * pow17_20 z = pow17_40_q z * f z + pow17_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_40_mul_integer z


theorem pow17_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_20 z * pow17_20 z = pow17_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_40_mul z


theorem pow17_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 40 = pow17_40 z := by
  calc
    _ = u16 z ^ 20 * u16 z ^ 20 := by ring
    _ = pow17_20 z * pow17_20 z := by rw [pow17_20_pow z hz]
    _ = _ := pow17_40_root z hz


def pow17_41 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (9 + z * (39 + z * (20 + z * (17 + z * (14 + z * (34 + z * (29 + z * (18 + z * (11 + z * (3 + z * (26 + z * (37 + z * (1 + z * (26 + z * (38 + z * (20 + z * (20 + z * (11 + z * 34)))))))))))))))))))

def pow17_41_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (10 + z * (26 + z * (33 + z * (11 + z * (6 + z * (34 + z * (30 + z * (38 + z * (16 + z * (39 + z * (22 + z * (39 + z * (38 + z * (22 + z * (10 + z * (9 + z * (6 + z * 12))))))))))))))))))

def pow17_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * ((-5) + z * ((-12) + z * ((-6) + z * ((-16) + z * (38 + z * (6 + z * (11 + z * (13 + z * (36 + z * (4 + z * (28 + z * (19 + z * (21 + z * ((-12) + z * (19 + z * (41 + z * (5 + z * (49 + z * (25 + z * (50 + z * (37 + z * (2 + z * (40 + z * (7 + z * (6 + z * ((-10) + z * ((-36) + z * ((-24) + z * ((-26) + z * (1 + z * ((-4) + z * (1 + z * (36 + z * (35 + z * (40 + z * (36 + z * (23 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow17_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_40 z * u16 z = pow17_41_q z * f z + pow17_41 z + (41 : R) * pow17_41_mul_t z := by
  simp only [pow17_40, u16, pow17_41_q, f, pow17_41, pow17_41_mul_t]
  simp only [pow16_41]
  ring

theorem pow17_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_40 z * u16 z = pow17_41_q z * f z + pow17_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_41_mul_integer z


theorem pow17_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_40 z * u16 z = pow17_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_41_mul z


theorem pow17_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 41 = pow17_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow17_40_pow z hz]
  exact pow17_41_root z hz


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_41 z

theorem iterate17 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 17) = u17 z := by
  calc
    _ = (z ^ (41 ^ 16)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate16 z hz)
    _ = _ := pow17_41_pow z hz


def pow18_2 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (30 + z * (17 + z * (31 + z * (23 + z * (40 + z * (12 + z * (11 + z * (21 + z * (39 + z * (29 + z * (4 + z * (15 + z * (15 + z * (20 + z * (34 + z * (10 + z * (26 + z * (33 + z * 31)))))))))))))))))))

def pow18_2_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (20 + z * (21 + z * (23 + z * (18 + z * (34 + z * (25 + z * (40 + z * (31 + z * (25 + z * (24 + z * (15 + z * (38 + z * (20 + z * (34 + z * (35 + z * (4 + z * (16 + z * 8))))))))))))))))))

def pow18_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (26 + z * ((-4) + z * (40 + z * (8 + z * (33 + z * ((-1) + z * (39 + z * (15 + z * (34 + z * (7 + z * ((-7) + z * (15 + z * (0 + z * (1 + z * (23 + z * (4 + z * ((-18) + z * (22 + z * (35 + z * (28 + z * ((-5) + z * (22 + z * ((-26) + z * ((-1) + z * ((-41) + z * ((-30) + z * (3 + z * (0 + z * ((-29) + z * ((-21) + z * (20 + z * (26 + z * ((-9) + z * (21 + z * (40 + z * (29 + z * (21 + z * (12 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow18_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z + (41 : R) * pow18_2_mul_t z := by
  simp only [u17, pow18_2_q, f, pow18_2, pow18_2_mul_t]
  simp only [pow17_41]
  ring

theorem pow18_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_2_mul_integer z


theorem pow18_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z * u17 z = pow18_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_2_mul z


theorem pow18_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 2 = pow18_2 z := by
  calc
    _ = u17 z ^ 1 * u17 z ^ 1 := by ring
    _ = u17 z * u17 z := by simp only [pow_one]
    _ = _ := pow18_2_root z hz


def pow18_4 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (27 + z * (34 + z * (6 + z * (9 + z * (10 + z * (24 + z * (33 + z * (40 + z * (6 + z * (35 + z * (5 + z * (36 + z * (5 + z * (33 + z * (40 + z * (24 + z * (39 + z * (7 + z * 23)))))))))))))))))))

def pow18_4_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (34 + z * (28 + z * (21 + z * (31 + z * (16 + z * (33 + z * (34 + z * (11 + z * (28 + z * (33 + z * (17 + z * (10 + z * (29 + z * (29 + z * (22 + z * (19 + z * (30 + z * 18))))))))))))))))))

def pow18_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-14) + z * ((-22) + z * ((-1) + z * ((-7) + z * (24 + z * (27 + z * ((-4) + z * (2 + z * (19 + z * (42 + z * ((-10) + z * (17 + z * (19 + z * (0 + z * ((-3) + z * ((-33) + z * ((-48) + z * (17 + z * (48 + z * (37 + z * ((-15) + z * (38 + z * (48 + z * (28 + z * ((-38) + z * ((-8) + z * (51 + z * (18 + z * ((-17) + z * ((-12) + z * ((-3) + z * (2 + z * (16 + z * (28 + z * (20 + z * (36 + z * (36 + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow18_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z + (41 : R) * pow18_4_mul_t z := by
  simp only [pow18_2, pow18_4_q, f, pow18_4, pow18_4_mul_t]
  
  ring

theorem pow18_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_4_mul_integer z


theorem pow18_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_2 z * pow18_2 z = pow18_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_4_mul z


theorem pow18_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 4 = pow18_4 z := by
  calc
    _ = u17 z ^ 2 * u17 z ^ 2 := by ring
    _ = pow18_2 z * pow18_2 z := by rw [pow18_2_pow z hz]
    _ = _ := pow18_4_root z hz


def pow18_5 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (1 + z * (29 + z * (11 + z * (25 + z * (24 + z * (35 + z * (29 + z * (25 + z * (34 + z * (27 + z * (7 + z * (5 + z * (21 + z * (39 + z * (28 + z * (1 + z * (13 + z * (27 + z * 9)))))))))))))))))))

def pow18_5_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (28 + z * (1 + z * (32 + z * (31 + z * (20 + z * (11 + z * (30 + z * (33 + z * (36 + z * (7 + z * (22 + z * (10 + z * (23 + z * (29 + z * (26 + z * (32 + z * (32 + z * 3))))))))))))))))))

def pow18_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-4) + z * (32 + z * (2 + z * (7 + z * ((-23) + z * (35 + z * (11 + z * (23 + z * (6 + z * (36 + z * ((-39) + z * (51 + z * (22 + z * (62 + z * ((-7) + z * (13 + z * (39 + z * (7 + z * (43 + z * (13 + z * (55 + z * (29 + z * (10 + z * ((-4) + z * (8 + z * (30 + z * (23 + z * ((-15) + z * (49 + z * (1 + z * (32 + z * ((-14) + z * (11 + z * (30 + z * (6 + z * (20 + z * (9 + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow18_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_4 z * u17 z = pow18_5_q z * f z + pow18_5 z + (41 : R) * pow18_5_mul_t z := by
  simp only [pow18_4, u17, pow18_5_q, f, pow18_5, pow18_5_mul_t]
  simp only [pow17_41]
  ring

theorem pow18_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_4 z * u17 z = pow18_5_q z * f z + pow18_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_5_mul_integer z


theorem pow18_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_4 z * u17 z = pow18_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_5_mul z


theorem pow18_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 5 = pow18_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow18_4_pow z hz]
  exact pow18_5_root z hz


def pow18_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (37 + z * (29 + z * (25 + z * (2 + z * (3 + z * (20 + z * (6 + z * (31 + z * (39 + z * (34 + z * (4 + z * (8 + z * (22 + z * (12 + z * (5 + z * (38 + z * (18 + z * (19 + z * 8)))))))))))))))))))

def pow18_10_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (5 + z * (6 + z * (4 + z * (30 + z * (17 + z * (13 + z * (14 + z * (28 + z * (1 + z * (1 + z * (33 + z * (39 + z * (28 + z * (19 + z * (38 + z * (14 + z * (24 + z * 40))))))))))))))))))

def pow18_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-13) + z * ((-11) + z * ((-3) + z * ((-18) + z * ((-5) + z * (13 + z * (10 + z * (12 + z * (56 + z * (71 + z * (50 + z * (40 + z * (51 + z * (57 + z * (6 + z * (42 + z * (48 + z * (14 + z * ((-3) + z * (46 + z * (54 + z * ((-2) + z * (30 + z * (47 + z * ((-19) + z * ((-49) + z * ((-26) + z * ((-11) + z * ((-61) + z * ((-87) + z * ((-60) + z * ((-29) + z * ((-38) + z * ((-62) + z * ((-26) + z * ((-11) + z * ((-18) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow18_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_5 z * pow18_5 z = pow18_10_q z * f z + pow18_10 z + (41 : R) * pow18_10_mul_t z := by
  simp only [pow18_5, pow18_10_q, f, pow18_10, pow18_10_mul_t]
  
  ring

theorem pow18_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_5 z * pow18_5 z = pow18_10_q z * f z + pow18_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_10_mul_integer z


theorem pow18_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_5 z * pow18_5 z = pow18_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_10_mul z


theorem pow18_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 10 = pow18_10 z := by
  calc
    _ = u17 z ^ 5 * u17 z ^ 5 := by ring
    _ = pow18_5 z * pow18_5 z := by rw [pow18_5_pow z hz]
    _ = _ := pow18_10_root z hz


def pow18_20 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (34 + z * (10 + z * (19 + z * (19 + z * (38 + z * (17 + z * (16 + z * (28 + z * (35 + z * (40 + z * (17 + z * (32 + z * (7 + z * (4 + z * (26 + z * (17 + z * (29 + z * (20 + z * 34)))))))))))))))))))

def pow18_20_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (12 + z * (16 + z * (36 + z * (34 + z * (30 + z * (31 + z * (0 + z * (40 + z * (12 + z * (36 + z * (39 + z * (39 + z * (6 + z * (18 + z * (29 + z * (30 + z * (24 + z * 23))))))))))))))))))

def pow18_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-9) + z * (7 + z * (12 + z * ((-4) + z * ((-37) + z * ((-49) + z * ((-36) + z * ((-60) + z * (21 + z * ((-10) + z * (29 + z * ((-60) + z * ((-62) + z * ((-62) + z * ((-74) + z * ((-72) + z * ((-35) + z * ((-31) + z * ((-53) + z * ((-90) + z * ((-96) + z * ((-94) + z * ((-95) + z * ((-56) + z * ((-50) + z * ((-23) + z * ((-74) + z * ((-62) + z * ((-66) + z * ((-68) + z * ((-67) + z * ((-29) + z * ((-39) + z * ((-21) + z * ((-14) + z * ((-12) + z * ((-10) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow18_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_10 z * pow18_10 z = pow18_20_q z * f z + pow18_20 z + (41 : R) * pow18_20_mul_t z := by
  simp only [pow18_10, pow18_20_q, f, pow18_20, pow18_20_mul_t]
  
  ring

theorem pow18_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_10 z * pow18_10 z = pow18_20_q z * f z + pow18_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_20_mul_integer z


theorem pow18_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_10 z * pow18_10 z = pow18_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_20_mul z


theorem pow18_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 20 = pow18_20 z := by
  calc
    _ = u17 z ^ 10 * u17 z ^ 10 := by ring
    _ = pow18_10 z * pow18_10 z := by rw [pow18_10_pow z hz]
    _ = _ := pow18_20_root z hz


def pow18_40 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (19 + z * (21 + z * (12 + z * (14 + z * (5 + z * (0 + z * (16 + z * (14 + z * (38 + z * (40 + z * (31 + z * (35 + z * (1 + z * (25 + z * (23 + z * (25 + z * (14 + z * (2 + z * 7)))))))))))))))))))

def pow18_40_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (3 + z * (23 + z * (20 + z * (21 + z * (10 + z * (26 + z * (27 + z * (18 + z * (6 + z * (30 + z * (22 + z * (39 + z * (5 + z * (30 + z * (36 + z * (1 + z * (13 + z * 8))))))))))))))))))

def pow18_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-1) + z * ((-12) + z * ((-5) + z * ((-25) + z * (17 + z * (26 + z * ((-13) + z * (8 + z * (46 + z * (47 + z * (46 + z * (27 + z * (95 + z * (7 + z * (29 + z * (40 + z * (45 + z * (56 + z * (28 + z * (145 + z * (47 + z * (45 + z * (41 + z * (84 + z * (35 + z * (21 + z * (80 + z * (54 + z * (23 + z * ((-8) + z * (0 + z * (5 + z * (1 + z * (39 + z * (45 + z * (45 + z * (27 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow18_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_20 z * pow18_20 z = pow18_40_q z * f z + pow18_40 z + (41 : R) * pow18_40_mul_t z := by
  simp only [pow18_20, pow18_40_q, f, pow18_40, pow18_40_mul_t]
  
  ring

theorem pow18_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_20 z * pow18_20 z = pow18_40_q z * f z + pow18_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_40_mul_integer z


theorem pow18_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_20 z * pow18_20 z = pow18_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_40_mul z


theorem pow18_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 40 = pow18_40 z := by
  calc
    _ = u17 z ^ 20 * u17 z ^ 20 := by ring
    _ = pow18_20 z * pow18_20 z := by rw [pow18_20_pow z hz]
    _ = _ := pow18_40_root z hz


def pow18_41 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (30 + z * (36 + z * (31 + z * (11 + z * (39 + z * (17 + z * (26 + z * (7 + z * (11 + z * (5 + z * (8 + z * (12 + z * (9 + z * (5 + z * (8 + z * (33 + z * (10 + z * (5 + z * 29)))))))))))))))))))

def pow18_41_q {R : Type*} [CommRing R] (z : R) : R := (9 + z * (34 + z * (3 + z * (9 + z * (26 + z * (31 + z * (14 + z * (11 + z * (18 + z * (26 + z * (16 + z * (37 + z * (35 + z * (34 + z * (14 + z * (25 + z * (7 + z * (16 + z * 33))))))))))))))))))

def pow18_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (21 + z * ((-10) + z * (34 + z * (15 + z * (22 + z * ((-22) + z * (16 + z * (24 + z * ((-10) + z * (13 + z * (29 + z * (19 + z * (21 + z * ((-14) + z * (55 + z * (12 + z * (41 + z * (30 + z * (15 + z * ((-4) + z * ((-57) + z * (16 + z * ((-25) + z * ((-2) + z * ((-10) + z * ((-31) + z * (5 + z * ((-14) + z * ((-19) + z * ((-22) + z * ((-21) + z * (1 + z * ((-40) + z * ((-15) + z * ((-17) + z * ((-2) + z * ((-10) + z * ((-21) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow18_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_40 z * u17 z = pow18_41_q z * f z + pow18_41 z + (41 : R) * pow18_41_mul_t z := by
  simp only [pow18_40, u17, pow18_41_q, f, pow18_41, pow18_41_mul_t]
  simp only [pow17_41]
  ring

theorem pow18_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_40 z * u17 z = pow18_41_q z * f z + pow18_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_41_mul_integer z


theorem pow18_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_40 z * u17 z = pow18_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_41_mul z


theorem pow18_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 41 = pow18_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow18_40_pow z hz]
  exact pow18_41_root z hz


abbrev u18 {R : Type*} [CommRing R] (z : R) : R := pow18_41 z

theorem iterate18 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 18) = u18 z := by
  calc
    _ = (z ^ (41 ^ 17)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u17 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate17 z hz)
    _ = _ := pow18_41_pow z hz

end DimensionTen.Mod41

end

end OAI
