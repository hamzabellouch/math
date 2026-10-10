import OAI.Analysis.Quantum.DimensionTen.Mod41Model

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow1_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 1))

def pow1_2_q {R : Type*} [CommRing R] (_ : R) : R := 0

def pow1_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 0))

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (41 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


def pow1_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 1))))

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 0))))

theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (41 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


def pow1_5 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1)))))

abbrev pow1_5_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0)))))

theorem pow1_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * u0 z = pow1_5_q z * f z + pow1_5 z + (41 : R) * pow1_5_mul_t z := by
  simp only [pow1_4, u0, pow1_5_q, f, pow1_5, pow1_5_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_4 z * u0 z = pow1_5_q z * f z + pow1_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_5_mul_integer z


theorem pow1_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_4 z * u0 z = pow1_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_5_mul z


theorem pow1_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 5 = pow1_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow1_4_pow z hz]
  exact pow1_5_root z hz


def pow1_10 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))))

abbrev pow1_10_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))))

theorem pow1_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_5 z * pow1_5 z = pow1_10_q z * f z + pow1_10 z + (41 : R) * pow1_10_mul_t z := by
  simp only [pow1_5, pow1_10_q, f, pow1_10, pow1_10_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_5 z * pow1_5 z = pow1_10_q z * f z + pow1_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_10_mul_integer z


theorem pow1_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_5 z * pow1_5 z = pow1_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_10_mul z


theorem pow1_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 10 = pow1_10 z := by
  calc
    _ = u0 z ^ 5 * u0 z ^ 5 := by ring
    _ = pow1_5 z * pow1_5 z := by rw [pow1_5_pow z hz]
    _ = _ := pow1_10_root z hz


def pow1_20 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (28 + z * (11 + z * (40 + z * (9 + z * (36 + z * (40 + z * (8 + z * (21 + z * (30 + z * (26 + z * (10 + z * (27 + z * (34 + z * (16 + z * (5 + z * (8 + z * (18 + z * (24 + z * 11)))))))))))))))))))

def pow1_20_q {R : Type*} [CommRing R] (_ : R) : R := 1

def pow1_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * ((-1) + z * 0))))))))))))))))))))

theorem pow1_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_10 z * pow1_10 z = pow1_20_q z * f z + pow1_20 z + (41 : R) * pow1_20_mul_t z := by
  simp only [pow1_10, pow1_20_q, f, pow1_20, pow1_20_mul_t]
  
  ring

theorem pow1_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_10 z * pow1_10 z = pow1_20_q z * f z + pow1_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_20_mul_integer z


theorem pow1_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_10 z * pow1_10 z = pow1_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_20_mul z


theorem pow1_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 20 = pow1_20 z := by
  calc
    _ = u0 z ^ 10 * u0 z ^ 10 := by ring
    _ = pow1_10 z * pow1_10 z := by rw [pow1_10_pow z hz]
    _ = _ := pow1_20_root z hz


def pow1_40 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (29 + z * (4 + z * (17 + z * (36 + z * (5 + z * (32 + z * (16 + z * (37 + z * (38 + z * (30 + z * (9 + z * (27 + z * (37 + z * (9 + z * (39 + z * (33 + z * (35 + z * (36 + z * 16)))))))))))))))))))

def pow1_40_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (30 + z * (22 + z * (36 + z * (40 + z * (14 + z * (2 + z * (30 + z * (3 + z * (40 + z * (28 + z * (0 + z * (24 + z * (5 + z * (27 + z * (37 + z * (12 + z * (14 + z * 39))))))))))))))))))

def pow1_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-31) + z * ((-32) + z * ((-37) + z * ((-31) + z * ((-37) + z * (44 + z * ((-4) + z * (18 + z * (17 + z * (18 + z * (14 + z * (23 + z * (56 + z * (17 + z * (43 + z * ((-16) + z * ((-31) + z * ((-11) + z * ((-16) + z * ((-25) + z * (12 + z * (1 + z * (17 + z * (10 + z * ((-34) + z * ((-31) + z * (5 + z * ((-36) + z * ((-55) + z * ((-17) + z * ((-20) + z * ((-39) + z * ((-66) + z * ((-52) + z * ((-12) + z * ((-3) + z * ((-16) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow1_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_20 z * pow1_20 z = pow1_40_q z * f z + pow1_40 z + (41 : R) * pow1_40_mul_t z := by
  simp only [pow1_20, pow1_40_q, f, pow1_40, pow1_40_mul_t]
  
  ring

theorem pow1_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_20 z * pow1_20 z = pow1_40_q z * f z + pow1_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_40_mul_integer z


theorem pow1_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_20 z * pow1_20 z = pow1_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_40_mul z


theorem pow1_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 40 = pow1_40 z := by
  calc
    _ = u0 z ^ 20 * u0 z ^ 20 := by ring
    _ = pow1_20 z * pow1_20 z := by rw [pow1_20_pow z hz]
    _ = _ := pow1_40_root z hz


def pow1_41 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (28 + z * (0 + z * (29 + z * (38 + z * (38 + z * (30 + z * (37 + z * (24 + z * (25 + z * (3 + z * (26 + z * (31 + z * (38 + z * (6 + z * (7 + z * (3 + z * (34 + z * (9 + z * 7)))))))))))))))))))

def pow1_41_q {R : Type*} [CommRing R] (_ : R) : R := 16

def pow1_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-5) + z * ((-11) + z * ((-1) + z * ((-13) + z * ((-2) + z * ((-1) + z * ((-13) + z * ((-8) + z * ((-4) + z * ((-5) + z * ((-12) + z * ((-6) + z * ((-3) + z * ((-9) + z * ((-14) + z * ((-12) + z * ((-9) + z * ((-6) + z * ((-11) + z * 0))))))))))))))))))))

theorem pow1_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_40 z * u0 z = pow1_41_q z * f z + pow1_41 z + (41 : R) * pow1_41_mul_t z := by
  simp only [pow1_40, u0, pow1_41_q, f, pow1_41, pow1_41_mul_t]
  
  ring

theorem pow1_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_40 z * u0 z = pow1_41_q z * f z + pow1_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_41_mul_integer z


theorem pow1_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_40 z * u0 z = pow1_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_41_mul z


theorem pow1_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 41 = pow1_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow1_40_pow z hz]
  exact pow1_41_root z hz


abbrev u1 {R : Type*} [CommRing R] (z : R) : R := pow1_41 z

theorem iterate1 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 1) = u1 z := by
  calc
    _ = (z ^ (41 ^ 0)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 41 := congrArg (fun x : R => x ^ 41) (initial z )
    _ = _ := pow1_41_pow z hz


def pow2_2 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (16 + z * (13 + z * (19 + z * (39 + z * (9 + z * (15 + z * (38 + z * (38 + z * (18 + z * (4 + z * (38 + z * (29 + z * (20 + z * (28 + z * (2 + z * (33 + z * (20 + z * (6 + z * 25)))))))))))))))))))

def pow2_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (16 + z * (16 + z * (15 + z * (9 + z * (37 + z * (39 + z * (12 + z * (2 + z * (24 + z * (1 + z * (19 + z * (40 + z * (14 + z * (20 + z * (10 + z * (28 + z * (9 + z * 8))))))))))))))))))

def pow2_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * (29 + z * ((-23) + z * (24 + z * (62 + z * (61 + z * (61 + z * (75 + z * (112 + z * (102 + z * (102 + z * (113 + z * (151 + z * (125 + z * (84 + z * (74 + z * (41 + z * (122 + z * (112 + z * (35 + z * (44 + z * (33 + z * (39 + z * ((-1) + z * (40 + z * (20 + z * (19 + z * ((-55) + z * ((-35) + z * ((-9) + z * (3 + z * ((-48) + z * ((-33) + z * ((-39) + z * (1 + z * ((-13) + z * (3 + z * ((-3) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow2_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z + (41 : R) * pow2_2_mul_t z := by
  simp only [u1, pow2_2_q, f, pow2_2, pow2_2_mul_t]
  simp only [pow1_41]
  ring

theorem pow2_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_2_mul_integer z


theorem pow2_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z * u1 z = pow2_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_2_mul z


theorem pow2_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 2 = pow2_2 z := by
  calc
    _ = u1 z ^ 1 * u1 z ^ 1 := by ring
    _ = u1 z * u1 z := by simp only [pow_one]
    _ = _ := pow2_2_root z hz


def pow2_4 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (19 + z * (32 + z * (36 + z * (19 + z * (27 + z * (18 + z * (26 + z * (35 + z * (11 + z * (22 + z * (22 + z * (22 + z * (37 + z * (21 + z * (14 + z * (3 + z * (17 + z * (22 + z * 33)))))))))))))))))))

def pow2_4_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (6 + z * (34 + z * (4 + z * (39 + z * (24 + z * (0 + z * (30 + z * (10 + z * (11 + z * (6 + z * (37 + z * (15 + z * (26 + z * (35 + z * (34 + z * (5 + z * (0 + z * 10))))))))))))))))))

def pow2_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * (10 + z * ((-32) + z * (23 + z * ((-4) + z * (11 + z * (2 + z * (36 + z * (76 + z * (17 + z * (54 + z * (54 + z * (83 + z * (40 + z * (55 + z * (26 + z * (70 + z * (59 + z * (33 + z * (59 + z * (103 + z * (41 + z * (19 + z * (68 + z * (66 + z * (61 + z * (7 + z * (48 + z * (29 + z * ((-30) + z * (7 + z * ((-4) + z * ((-2) + z * (15 + z * ((-14) + z * (36 + z * (21 + z * (0 + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow2_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z + (41 : R) * pow2_4_mul_t z := by
  simp only [pow2_2, pow2_4_q, f, pow2_4, pow2_4_mul_t]
  
  ring

theorem pow2_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_4_mul_integer z


theorem pow2_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_2 z * pow2_2 z = pow2_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_4_mul z


theorem pow2_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 4 = pow2_4 z := by
  calc
    _ = u1 z ^ 2 * u1 z ^ 2 := by ring
    _ = pow2_2 z * pow2_2 z := by rw [pow2_2_pow z hz]
    _ = _ := pow2_4_root z hz


def pow2_5 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (8 + z * (2 + z * (23 + z * (11 + z * (4 + z * (32 + z * (4 + z * (29 + z * (24 + z * (22 + z * (16 + z * (36 + z * (25 + z * (30 + z * (5 + z * (5 + z * (8 + z * (20 + z * 8)))))))))))))))))))

def pow2_5_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (2 + z * (23 + z * (21 + z * (2 + z * (26 + z * (40 + z * (21 + z * (1 + z * (33 + z * (35 + z * (24 + z * (36 + z * (36 + z * (6 + z * (11 + z * (2 + z * (40 + z * 26))))))))))))))))))

def pow2_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (14 + z * ((-6) + z * (38 + z * (14 + z * (47 + z * (54 + z * (40 + z * (107 + z * (68 + z * (46 + z * (63 + z * (75 + z * (56 + z * (68 + z * (84 + z * (56 + z * (2 + z * (57 + z * (55 + z * (43 + z * ((-14) + z * (17 + z * (34 + z * ((-9) + z * ((-15) + z * ((-5) + z * ((-32) + z * ((-75) + z * ((-64) + z * (12 + z * ((-6) + z * ((-29) + z * ((-47) + z * ((-28) + z * ((-8) + z * ((-5) + z * ((-9) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow2_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_4 z * u1 z = pow2_5_q z * f z + pow2_5 z + (41 : R) * pow2_5_mul_t z := by
  simp only [pow2_4, u1, pow2_5_q, f, pow2_5, pow2_5_mul_t]
  simp only [pow1_41]
  ring

theorem pow2_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_4 z * u1 z = pow2_5_q z * f z + pow2_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_5_mul_integer z


theorem pow2_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_4 z * u1 z = pow2_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_5_mul z


theorem pow2_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 5 = pow2_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow2_4_pow z hz]
  exact pow2_5_root z hz


def pow2_10 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (38 + z * (10 + z * (14 + z * (36 + z * (4 + z * (25 + z * (23 + z * (14 + z * (13 + z * (12 + z * (12 + z * (23 + z * (21 + z * (24 + z * (2 + z * (4 + z * (16 + z * (29 + z * 17)))))))))))))))))))

def pow2_10_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (25 + z * (12 + z * (35 + z * (26 + z * (22 + z * (37 + z * (34 + z * (23 + z * (21 + z * (18 + z * (24 + z * (31 + z * (9 + z * (0 + z * (3 + z * (3 + z * (40 + z * 23))))))))))))))))))

def pow2_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-32) + z * ((-39) + z * ((-52) + z * ((-58) + z * ((-70) + z * ((-56) + z * ((-87) + z * ((-105) + z * ((-52) + z * ((-89) + z * ((-95) + z * ((-67) + z * ((-73) + z * ((-63) + z * ((-49) + z * ((-52) + z * ((-82) + z * ((-69) + z * ((-110) + z * ((-41) + z * ((-51) + z * ((-43) + z * ((-37) + z * ((-25) + z * ((-44) + z * ((-12) + z * ((-20) + z * ((-36) + z * ((-30) + z * (4 + z * ((-9) + z * ((-19) + z * ((-37) + z * ((-36) + z * ((-22) + z * ((-26) + z * ((-10) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow2_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_5 z * pow2_5 z = pow2_10_q z * f z + pow2_10 z + (41 : R) * pow2_10_mul_t z := by
  simp only [pow2_5, pow2_10_q, f, pow2_10, pow2_10_mul_t]
  
  ring

theorem pow2_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_5 z * pow2_5 z = pow2_10_q z * f z + pow2_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_10_mul_integer z


theorem pow2_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_5 z * pow2_5 z = pow2_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_10_mul z


theorem pow2_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 10 = pow2_10 z := by
  calc
    _ = u1 z ^ 5 * u1 z ^ 5 := by ring
    _ = pow2_5 z * pow2_5 z := by rw [pow2_5_pow z hz]
    _ = _ := pow2_10_root z hz


def pow2_20 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (28 + z * (12 + z * (16 + z * (18 + z * (14 + z * (12 + z * (10 + z * (21 + z * (12 + z * (23 + z * (11 + z * (8 + z * (38 + z * (39 + z * (31 + z * (32 + z * (27 + z * (7 + z * 25)))))))))))))))))))

def pow2_20_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (39 + z * (40 + z * (4 + z * (29 + z * (29 + z * (28 + z * (28 + z * (37 + z * (21 + z * (0 + z * (38 + z * (10 + z * (39 + z * (30 + z * (7 + z * (16 + z * (24 + z * 2))))))))))))))))))

def pow2_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * (10 + z * ((-15) + z * ((-8) + z * (3 + z * (7 + z * ((-28) + z * (22 + z * ((-21) + z * ((-56) + z * (5 + z * ((-43) + z * ((-32) + z * ((-42) + z * (2 + z * ((-82) + z * ((-102) + z * ((-88) + z * ((-47) + z * ((-44) + z * ((-66) + z * ((-85) + z * ((-54) + z * ((-75) + z * ((-77) + z * ((-46) + z * ((-33) + z * ((-60) + z * ((-66) + z * ((-45) + z * ((-35) + z * ((-8) + z * ((-27) + z * ((-30) + z * ((-14) + z * (3 + z * (15 + z * (22 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow2_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_10 z * pow2_10 z = pow2_20_q z * f z + pow2_20 z + (41 : R) * pow2_20_mul_t z := by
  simp only [pow2_10, pow2_20_q, f, pow2_20, pow2_20_mul_t]
  
  ring

theorem pow2_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_10 z * pow2_10 z = pow2_20_q z * f z + pow2_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_20_mul_integer z


theorem pow2_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_10 z * pow2_10 z = pow2_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_20_mul z


theorem pow2_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 20 = pow2_20 z := by
  calc
    _ = u1 z ^ 10 * u1 z ^ 10 := by ring
    _ = pow2_10 z * pow2_10 z := by rw [pow2_10_pow z hz]
    _ = _ := pow2_20_root z hz


def pow2_40 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (17 + z * (32 + z * (28 + z * (11 + z * (36 + z * (22 + z * (18 + z * (6 + z * (28 + z * (17 + z * (25 + z * (31 + z * (5 + z * (30 + z * (16 + z * (9 + z * (25 + z * (1 + z * 10)))))))))))))))))))

def pow2_40_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (38 + z * (10 + z * (17 + z * (37 + z * (35 + z * (32 + z * (27 + z * (30 + z * (10 + z * (22 + z * (0 + z * (9 + z * (7 + z * (38 + z * (8 + z * (16 + z * (9 + z * 10))))))))))))))))))

def pow2_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * (4 + z * (0 + z * ((-5) + z * ((-10) + z * ((-32) + z * ((-25) + z * ((-40) + z * ((-59) + z * ((-29) + z * ((-24) + z * ((-24) + z * ((-64) + z * (22 + z * (12 + z * (9 + z * ((-3) + z * (32 + z * ((-4) + z * (14 + z * ((-7) + z * ((-21) + z * ((-12) + z * (4 + z * (10 + z * (3 + z * (43 + z * (83 + z * (73 + z * (82 + z * (90 + z * (64 + z * (73 + z * (44 + z * (40 + z * (27 + z * (23 + z * (1 + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow2_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_20 z * pow2_20 z = pow2_40_q z * f z + pow2_40 z + (41 : R) * pow2_40_mul_t z := by
  simp only [pow2_20, pow2_40_q, f, pow2_40, pow2_40_mul_t]
  
  ring

theorem pow2_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_20 z * pow2_20 z = pow2_40_q z * f z + pow2_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_40_mul_integer z


theorem pow2_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_20 z * pow2_20 z = pow2_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_40_mul z


theorem pow2_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 40 = pow2_40 z := by
  calc
    _ = u1 z ^ 20 * u1 z ^ 20 := by ring
    _ = pow2_20 z * pow2_20 z := by rw [pow2_20_pow z hz]
    _ = _ := pow2_40_root z hz


def pow2_41 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (29 + z * (27 + z * (31 + z * (36 + z * (9 + z * (34 + z * (26 + z * (19 + z * (35 + z * (20 + z * (7 + z * (26 + z * (24 + z * (18 + z * (25 + z * (35 + z * (27 + z * (34 + z * 29)))))))))))))))))))

def pow2_41_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (30 + z * (30 + z * (17 + z * (40 + z * (18 + z * (29 + z * (37 + z * (32 + z * (25 + z * (40 + z * (34 + z * (7 + z * (35 + z * (28 + z * (35 + z * (15 + z * (6 + z * 29))))))))))))))))))

def pow2_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-13) + z * ((-23) + z * (11 + z * ((-39) + z * (24 + z * (32 + z * (16 + z * ((-12) + z * (29 + z * (21 + z * ((-24) + z * (22 + z * (7 + z * (15 + z * ((-38) + z * ((-25) + z * ((-36) + z * ((-47) + z * ((-50) + z * ((-49) + z * ((-59) + z * ((-64) + z * ((-50) + z * ((-53) + z * ((-106) + z * ((-84) + z * ((-67) + z * ((-54) + z * ((-78) + z * ((-70) + z * ((-40) + z * ((-57) + z * ((-55) + z * ((-32) + z * ((-22) + z * ((-4) + z * ((-19) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow2_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_40 z * u1 z = pow2_41_q z * f z + pow2_41 z + (41 : R) * pow2_41_mul_t z := by
  simp only [pow2_40, u1, pow2_41_q, f, pow2_41, pow2_41_mul_t]
  simp only [pow1_41]
  ring

theorem pow2_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_40 z * u1 z = pow2_41_q z * f z + pow2_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_41_mul_integer z


theorem pow2_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_40 z * u1 z = pow2_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_41_mul z


theorem pow2_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 41 = pow2_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow2_40_pow z hz]
  exact pow2_41_root z hz


abbrev u2 {R : Type*} [CommRing R] (z : R) : R := pow2_41 z

theorem iterate2 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 2) = u2 z := by
  calc
    _ = (z ^ (41 ^ 1)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u1 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate1 z hz)
    _ = _ := pow2_41_pow z hz

end DimensionTen.Mod41

end

end OAI
