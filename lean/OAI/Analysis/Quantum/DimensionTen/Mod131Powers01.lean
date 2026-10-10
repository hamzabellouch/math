import OAI.Analysis.Quantum.DimensionTen.Mod131Model

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow1_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 1))

def pow1_2_q {R : Type*} [CommRing R] (_ : R) : R := 0

def pow1_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 0))

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (131 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


def pow1_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 1))))

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 0))))

theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (131 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


def pow1_8 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))

abbrev pow1_8_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))

theorem pow1_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z + (131 : R) * pow1_8_mul_t z := by
  simp only [pow1_4, pow1_8_q, f, pow1_8, pow1_8_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_8_mul_integer z


theorem pow1_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_4 z * pow1_4 z = pow1_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_8_mul z


theorem pow1_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 8 = pow1_8 z := by
  calc
    _ = u0 z ^ 4 * u0 z ^ 4 := by ring
    _ = pow1_4 z * pow1_4 z := by rw [pow1_4_pow z hz]
    _ = _ := pow1_8_root z hz


def pow1_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))))))))))

abbrev pow1_16_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))))))))))

theorem pow1_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z + (131 : R) * pow1_16_mul_t z := by
  simp only [pow1_8, pow1_16_q, f, pow1_16, pow1_16_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_16_mul_integer z


theorem pow1_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_8 z * pow1_8 z = pow1_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_16_mul z


theorem pow1_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 16 = pow1_16 z := by
  calc
    _ = u0 z ^ 8 * u0 z ^ 8 := by ring
    _ = pow1_8 z * pow1_8 z := by rw [pow1_8_pow z hz]
    _ = _ := pow1_16_root z hz


def pow1_32 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (123 + z * (50 + z * (47 + z * (91 + z * (44 + z * (95 + z * (70 + z * (102 + z * (114 + z * (11 + z * (16 + z * (107 + z * (83 + z * (100 + z * (42 + z * (112 + z * (67 + z * (42 + z * 41)))))))))))))))))))

def pow1_32_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (48 + z * (12 + z * (105 + z * (7 + z * (65 + z * (12 + z * (25 + z * (2 + z * (59 + z * (105 + z * (65 + z * 1))))))))))))

def pow1_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-25) + z * ((-30) + z * ((-71) + z * ((-64) + z * ((-121) + z * ((-99) + z * ((-124) + z * ((-161) + z * ((-131) + z * ((-217) + z * ((-226) + z * ((-247) + z * ((-209) + z * ((-301) + z * ((-250) + z * ((-253) + z * ((-211) + z * ((-271) + z * ((-235) + z * ((-202) + z * ((-245) + z * ((-256) + z * ((-163) + z * ((-110) + z * ((-91) + z * ((-123) + z * ((-110) + z * ((-102) + z * ((-83) + z * ((-34) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))

theorem pow1_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_16 z * pow1_16 z = pow1_32_q z * f z + pow1_32 z + (131 : R) * pow1_32_mul_t z := by
  simp only [pow1_16, pow1_32_q, f, pow1_32, pow1_32_mul_t]
  
  ring

theorem pow1_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_16 z * pow1_16 z = pow1_32_q z * f z + pow1_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_32_mul_integer z


theorem pow1_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_16 z * pow1_16 z = pow1_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_32_mul z


theorem pow1_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 32 = pow1_32 z := by
  calc
    _ = u0 z ^ 16 * u0 z ^ 16 := by ring
    _ = pow1_16 z * pow1_16 z := by rw [pow1_16_pow z hz]
    _ = _ := pow1_32_root z hz


def pow1_64 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (24 + z * (123 + z * (9 + z * (2 + z * (0 + z * (1 + z * (35 + z * (53 + z * (88 + z * (90 + z * (65 + z * (119 + z * (67 + z * (83 + z * (105 + z * (68 + z * (96 + z * (118 + z * 109)))))))))))))))))))

def pow1_64_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (124 + z * (2 + z * (114 + z * (120 + z * (51 + z * (66 + z * (120 + z * (65 + z * (79 + z * (78 + z * (54 + z * (16 + z * (114 + z * (13 + z * (120 + z * (82 + z * (49 + z * 109))))))))))))))))))

def pow1_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (91 + z * (160 + z * (142 + z * (67 + z * (142 + z * (70 + z * (107 + z * (203 + z * (115 + z * (210 + z * (197 + z * ((-50) + z * (52 + z * (266 + z * (201 + z * (141 + z * (236 + z * (240 + z * (162 + z * (80 + z * (68 + z * (174 + z * (78 + z * (25 + z * (77 + z * (142 + z * ((-12) + z * (17 + z * (87 + z * (1 + z * (124 + z * (61 + z * (73 + z * (49 + z * ((-55) + z * (8 + z * ((-19) + z * ((-29) + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow1_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_32 z * pow1_32 z = pow1_64_q z * f z + pow1_64 z + (131 : R) * pow1_64_mul_t z := by
  simp only [pow1_32, pow1_64_q, f, pow1_64, pow1_64_mul_t]
  
  ring

theorem pow1_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_32 z * pow1_32 z = pow1_64_q z * f z + pow1_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_64_mul_integer z


theorem pow1_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_32 z * pow1_32 z = pow1_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_64_mul z


theorem pow1_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 64 = pow1_64 z := by
  calc
    _ = u0 z ^ 32 * u0 z ^ 32 := by ring
    _ = pow1_32 z * pow1_32 z := by rw [pow1_32_pow z hz]
    _ = _ := pow1_64_root z hz


def pow1_65 {R : Type*} [CommRing R] (z : R) : R := (52 + z * (54 + z * (122 + z * (105 + z * (130 + z * (21 + z * (44 + z * (100 + z * (8 + z * (62 + z * (69 + z * (22 + z * (101 + z * (110 + z * (90 + z * (111 + z * (32 + z * (98 + z * (84 + z * 129)))))))))))))))))))

def pow1_65_q {R : Type*} [CommRing R] (_ : R) : R := 109

def pow1_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-42) + z * ((-39) + z * ((-54) + z * ((-19) + z * ((-60) + z * ((-95) + z * ((-2) + z * ((-59) + z * ((-83) + z * ((-45) + z * ((-14) + z * ((-96) + z * ((-71) + z * ((-64) + z * ((-6) + z * ((-31) + z * ((-71) + z * ((-41) + z * ((-49) + z * ((-55) + z * 0))))))))))))))))))))

theorem pow1_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_64 z * u0 z = pow1_65_q z * f z + pow1_65 z + (131 : R) * pow1_65_mul_t z := by
  simp only [pow1_64, u0, pow1_65_q, f, pow1_65, pow1_65_mul_t]
  
  ring

theorem pow1_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_64 z * u0 z = pow1_65_q z * f z + pow1_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_65_mul_integer z


theorem pow1_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_64 z * u0 z = pow1_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_65_mul z


theorem pow1_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 65 = pow1_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow1_64_pow z hz]
  exact pow1_65_root z hz


def pow1_130 {R : Type*} [CommRing R] (z : R) : R := (98 + z * (40 + z * (27 + z * (78 + z * (53 + z * (99 + z * (5 + z * (53 + z * (38 + z * (110 + z * (66 + z * (22 + z * (80 + z * (84 + z * (41 + z * (80 + z * (64 + z * (33 + z * (73 + z * 96)))))))))))))))))))

def pow1_130_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (27 + z * (118 + z * (75 + z * (35 + z * (118 + z * (104 + z * (51 + z * (8 + z * (23 + z * (1 + z * (66 + z * (82 + z * (94 + z * (94 + z * (99 + z * (47 + z * (55 + z * 4))))))))))))))))))

def pow1_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-9) + z * (8 + z * (79 + z * (138 + z * (89 + z * (177 + z * (37 + z * (52 + z * (72 + z * (34 + z * (27 + z * (44 + z * (37 + z * (157 + z * (195 + z * (278 + z * (292 + z * (151 + z * (398 + z * (339 + z * (450 + z * (342 + z * (227 + z * (135 + z * (207 + z * (304 + z * (275 + z * (281 + z * (300 + z * (243 + z * (326 + z * (332 + z * (220 + z * (238 + z * (138 + z * (217 + z * (163 + z * 127))))))))))))))))))))))))))))))))))))))

theorem pow1_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_65 z * pow1_65 z = pow1_130_q z * f z + pow1_130 z + (131 : R) * pow1_130_mul_t z := by
  simp only [pow1_65, pow1_130_q, f, pow1_130, pow1_130_mul_t]
  
  ring

theorem pow1_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_65 z * pow1_65 z = pow1_130_q z * f z + pow1_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_130_mul_integer z


theorem pow1_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_65 z * pow1_65 z = pow1_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_130_mul z


theorem pow1_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 130 = pow1_130 z := by
  calc
    _ = u0 z ^ 65 * u0 z ^ 65 := by ring
    _ = pow1_65 z * pow1_65 z := by rw [pow1_65_pow z hz]
    _ = _ := pow1_130_root z hz


def pow1_131 {R : Type*} [CommRing R] (z : R) : R := (47 + z * (40 + z * (53 + z * (46 + z * (74 + z * (113 + z * (38 + z * (97 + z * (16 + z * (94 + z * (50 + z * (65 + z * (115 + z * (24 + z * (67 + z * (26 + z * (77 + z * (76 + z * (2 + z * 25)))))))))))))))))))

def pow1_131_q {R : Type*} [CommRing R] (_ : R) : R := 96

def pow1_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-37) + z * ((-34) + z * ((-47) + z * ((-17) + z * ((-52) + z * ((-84) + z * ((-1) + z * ((-52) + z * ((-73) + z * ((-40) + z * ((-12) + z * ((-85) + z * ((-63) + z * ((-56) + z * ((-5) + z * ((-27) + z * ((-63) + z * ((-36) + z * ((-43) + z * ((-48) + z * 0))))))))))))))))))))

theorem pow1_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_130 z * u0 z = pow1_131_q z * f z + pow1_131 z + (131 : R) * pow1_131_mul_t z := by
  simp only [pow1_130, u0, pow1_131_q, f, pow1_131, pow1_131_mul_t]
  
  ring

theorem pow1_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow1_130 z * u0 z = pow1_131_q z * f z + pow1_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow1_131_mul_integer z


theorem pow1_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow1_130 z * u0 z = pow1_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_131_mul z


theorem pow1_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u0 z ^ 131 = pow1_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow1_130_pow z hz]
  exact pow1_131_root z hz


abbrev u1 {R : Type*} [CommRing R] (z : R) : R := pow1_131 z

theorem iterate1 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 1) = u1 z := by
  calc
    _ = (z ^ (131 ^ 0)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 131 := congrArg (fun x : R => x ^ 131) (initial z )
    _ = _ := pow1_131_pow z hz


def pow2_2 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (58 + z * (128 + z * (98 + z * (24 + z * (97 + z * (13 + z * (22 + z * (34 + z * (127 + z * (84 + z * (119 + z * (86 + z * (102 + z * (55 + z * (78 + z * (108 + z * (17 + z * (13 + z * 44)))))))))))))))))))

def pow2_2_q {R : Type*} [CommRing R] (z : R) : R := (107 + z * (18 + z * (80 + z * (14 + z * (66 + z * (48 + z * (75 + z * (85 + z * (124 + z * (41 + z * (130 + z * (121 + z * (72 + z * (16 + z * (13 + z * (109 + z * (80 + z * (115 + z * 101))))))))))))))))))

def pow2_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-17) + z * ((-40) + z * (3 + z * ((-28) + z * ((-3) + z * (31 + z * (7 + z * ((-41) + z * (10 + z * (1 + z * ((-84) + z * ((-37) + z * ((-132) + z * (114 + z * ((-163) + z * ((-6) + z * ((-46) + z * ((-136) + z * ((-147) + z * ((-200) + z * (16 + z * ((-186) + z * ((-193) + z * ((-104) + z * ((-171) + z * ((-134) + z * ((-223) + z * ((-117) + z * ((-169) + z * ((-137) + z * ((-56) + z * ((-59) + z * ((-74) + z * ((-144) + z * ((-99) + z * ((-75) + z * ((-51) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow2_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z + (131 : R) * pow2_2_mul_t z := by
  simp only [u1, pow2_2_q, f, pow2_2, pow2_2_mul_t]
  simp only [pow1_131]
  ring

theorem pow2_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_2_mul_integer z


theorem pow2_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z * u1 z = pow2_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_2_mul z


theorem pow2_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 2 = pow2_2 z := by
  calc
    _ = u1 z ^ 1 * u1 z ^ 1 := by ring
    _ = u1 z * u1 z := by simp only [pow_one]
    _ = _ := pow2_2_root z hz


def pow2_4 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (128 + z * (91 + z * (123 + z * (130 + z * (26 + z * (98 + z * (77 + z * (26 + z * (11 + z * (32 + z * (27 + z * (49 + z * (108 + z * (110 + z * (70 + z * (91 + z * (3 + z * (110 + z * 119)))))))))))))))))))

def pow2_4_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (11 + z * (40 + z * (101 + z * (60 + z * (27 + z * (72 + z * (97 + z * (15 + z * (84 + z * (39 + z * (116 + z * (10 + z * (97 + z * (54 + z * (125 + z * (13 + z * (45 + z * 102))))))))))))))))))

def pow2_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * ((-14) + z * ((-4) + z * (53 + z * (114 + z * (95 + z * (90 + z * (44 + z * ((-36) + z * ((-75) + z * (66 + z * (33 + z * (199 + z * (217 + z * (243 + z * (103 + z * (155 + z * (202 + z * (187 + z * (54 + z * (79 + z * (271 + z * (3 + z * (33 + z * (220 + z * (180 + z * (39 + z * (137 + z * (144 + z * (47 + z * ((-3) + z * (3 + z * (42 + z * ((-67) + z * ((-77) + z * (10 + z * ((-56) + z * ((-43) + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow2_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z + (131 : R) * pow2_4_mul_t z := by
  simp only [pow2_2, pow2_4_q, f, pow2_4, pow2_4_mul_t]
  
  ring

theorem pow2_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_4_mul_integer z


theorem pow2_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_2 z * pow2_2 z = pow2_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_4_mul z


theorem pow2_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 4 = pow2_4 z := by
  calc
    _ = u1 z ^ 2 * u1 z ^ 2 := by ring
    _ = pow2_2 z * pow2_2 z := by rw [pow2_2_pow z hz]
    _ = _ := pow2_4_root z hz


def pow2_8 {R : Type*} [CommRing R] (z : R) : R := (52 + z * (4 + z * (69 + z * (70 + z * (31 + z * (129 + z * (80 + z * (125 + z * (93 + z * (61 + z * (94 + z * (68 + z * (83 + z * (55 + z * (3 + z * (56 + z * (72 + z * (6 + z * (76 + z * 45)))))))))))))))))))

def pow2_8_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (61 + z * (24 + z * (84 + z * (126 + z * (64 + z * (34 + z * (31 + z * (100 + z * (69 + z * (39 + z * (58 + z * (55 + z * (115 + z * (110 + z * (37 + z * (41 + z * (39 + z * 13))))))))))))))))))

def pow2_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (82 + z * (183 + z * (232 + z * (311 + z * (406 + z * (290 + z * (335 + z * (439 + z * (230 + z * (109 + z * (193 + z * (49 + z * ((-43) + z * (90 + z * (254 + z * (211 + z * (278 + z * (296 + z * (351 + z * (487 + z * (401 + z * (187 + z * (276 + z * (121 + z * ((-21) + z * (93 + z * (94 + z * (47 + z * (117 + z * (137 + z * (113 + z * (206 + z * (287 + z * (204 + z * (219 + z * (127 + z * (72 + z * (193 + z * 108))))))))))))))))))))))))))))))))))))))

theorem pow2_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z + (131 : R) * pow2_8_mul_t z := by
  simp only [pow2_4, pow2_8_q, f, pow2_8, pow2_8_mul_t]
  
  ring

theorem pow2_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_8_mul_integer z


theorem pow2_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_4 z * pow2_4 z = pow2_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_8_mul z


theorem pow2_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 8 = pow2_8 z := by
  calc
    _ = u1 z ^ 4 * u1 z ^ 4 := by ring
    _ = pow2_4 z * pow2_4 z := by rw [pow2_4_pow z hz]
    _ = _ := pow2_8_root z hz


def pow2_16 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (44 + z * (129 + z * (3 + z * (104 + z * (64 + z * (85 + z * (87 + z * (127 + z * (77 + z * (35 + z * (125 + z * (49 + z * (84 + z * (16 + z * (107 + z * (94 + z * (60 + z * (94 + z * 126)))))))))))))))))))

def pow2_16_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (61 + z * (102 + z * (108 + z * (45 + z * (108 + z * (87 + z * (7 + z * (112 + z * (42 + z * (9 + z * (113 + z * (13 + z * (113 + z * (6 + z * (103 + z * (26 + z * (129 + z * 60))))))))))))))))))

def pow2_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * ((-33) + z * ((-24) + z * ((-54) + z * ((-71) + z * ((-14) + z * ((-81) + z * (11 + z * (24 + z * (42 + z * (93 + z * (84 + z * (221 + z * (48 + z * (131 + z * (193 + z * (61 + z * (80 + z * (133 + z * ((-17) + z * (21 + z * (72 + z * ((-64) + z * (166 + z * ((-29) + z * (62 + z * (15 + z * ((-6) + z * ((-13) + z * ((-80) + z * ((-79) + z * (5 + z * ((-69) + z * ((-88) + z * ((-29) + z * ((-38) + z * ((-44) + z * (21 + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow2_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z + (131 : R) * pow2_16_mul_t z := by
  simp only [pow2_8, pow2_16_q, f, pow2_16, pow2_16_mul_t]
  
  ring

theorem pow2_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_16_mul_integer z


theorem pow2_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_8 z * pow2_8 z = pow2_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_16_mul z


theorem pow2_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 16 = pow2_16 z := by
  calc
    _ = u1 z ^ 8 * u1 z ^ 8 := by ring
    _ = pow2_8 z * pow2_8 z := by rw [pow2_8_pow z hz]
    _ = _ := pow2_16_root z hz


def pow2_32 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (101 + z * (94 + z * (12 + z * (26 + z * (31 + z * (129 + z * (9 + z * (23 + z * (0 + z * (92 + z * (114 + z * (51 + z * (8 + z * (124 + z * (18 + z * (62 + z * (42 + z * (10 + z * 89)))))))))))))))))))

def pow2_32_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (47 + z * (50 + z * (106 + z * (93 + z * (37 + z * (5 + z * (84 + z * (68 + z * (109 + z * (49 + z * (4 + z * (108 + z * (116 + z * (19 + z * (42 + z * (65 + z * (30 + z * 25))))))))))))))))))

def pow2_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-10) + z * (29 + z * ((-1) + z * (57 + z * ((-61) + z * (147 + z * (43 + z * (115 + z * (114 + z * (229 + z * (140 + z * (118 + z * (290 + z * (63 + z * (292 + z * (152 + z * (333 + z * (263 + z * (450 + z * (320 + z * (373 + z * (374 + z * (474 + z * (428 + z * (290 + z * (430 + z * (415 + z * (242 + z * (207 + z * (342 + z * (207 + z * (214 + z * (190 + z * (290 + z * (211 + z * (156 + z * (168 + z * 121))))))))))))))))))))))))))))))))))))))

theorem pow2_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_16 z * pow2_16 z = pow2_32_q z * f z + pow2_32 z + (131 : R) * pow2_32_mul_t z := by
  simp only [pow2_16, pow2_32_q, f, pow2_32, pow2_32_mul_t]
  
  ring

theorem pow2_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_16 z * pow2_16 z = pow2_32_q z * f z + pow2_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_32_mul_integer z


theorem pow2_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_16 z * pow2_16 z = pow2_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_32_mul z


theorem pow2_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 32 = pow2_32 z := by
  calc
    _ = u1 z ^ 16 * u1 z ^ 16 := by ring
    _ = pow2_16 z * pow2_16 z := by rw [pow2_16_pow z hz]
    _ = _ := pow2_32_root z hz


def pow2_64 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (16 + z * (38 + z * (15 + z * (112 + z * (38 + z * (117 + z * (66 + z * (51 + z * (81 + z * (91 + z * (83 + z * (92 + z * (110 + z * (75 + z * (50 + z * (109 + z * (9 + z * (52 + z * 77)))))))))))))))))))

def pow2_64_q {R : Type*} [CommRing R] (z : R) : R := (77 + z * (2 + z * (5 + z * (58 + z * (8 + z * (39 + z * (114 + z * (6 + z * (7 + z * (48 + z * (60 + z * (43 + z * (98 + z * (18 + z * (5 + z * (122 + z * (122 + z * (112 + z * 61))))))))))))))))))

def pow2_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (27 + z * (89 + z * (113 + z * (31 + z * ((-41) + z * (79 + z * (112 + z * (40 + z * ((-25) + z * ((-43) + z * ((-12) + z * (271 + z * (33 + z * ((-49) + z * (33 + z * (139 + z * ((-49) + z * ((-48) + z * ((-182) + z * (90 + z * ((-29) + z * ((-72) + z * ((-203) + z * ((-107) + z * (67 + z * ((-81) + z * ((-107) + z * ((-140) + z * ((-88) + z * (65 + z * ((-49) + z * ((-102) + z * (17 + z * ((-151) + z * ((-45) + z * ((-27) + z * ((-18) + z * 60))))))))))))))))))))))))))))))))))))))

theorem pow2_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_32 z * pow2_32 z = pow2_64_q z * f z + pow2_64 z + (131 : R) * pow2_64_mul_t z := by
  simp only [pow2_32, pow2_64_q, f, pow2_64, pow2_64_mul_t]
  
  ring

theorem pow2_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_32 z * pow2_32 z = pow2_64_q z * f z + pow2_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_64_mul_integer z


theorem pow2_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_32 z * pow2_32 z = pow2_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_64_mul z


theorem pow2_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 64 = pow2_64 z := by
  calc
    _ = u1 z ^ 32 * u1 z ^ 32 := by ring
    _ = pow2_32 z * pow2_32 z := by rw [pow2_32_pow z hz]
    _ = _ := pow2_64_root z hz


def pow2_65 {R : Type*} [CommRing R] (z : R) : R := (71 + z * (21 + z * (125 + z * (11 + z * (70 + z * (118 + z * (103 + z * (44 + z * (71 + z * (111 + z * (34 + z * (94 + z * (39 + z * (95 + z * (72 + z * (67 + z * (108 + z * (24 + z * (112 + z * 57)))))))))))))))))))

def pow2_65_q {R : Type*} [CommRing R] (z : R) : R := (58 + z * (26 + z * (109 + z * (46 + z * (112 + z * (68 + z * (76 + z * (87 + z * (94 + z * (128 + z * (72 + z * (10 + z * (27 + z * (2 + z * (75 + z * (89 + z * (75 + z * (33 + z * 91))))))))))))))))))

def pow2_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-5) + z * ((-35) + z * ((-33) + z * ((-46) + z * ((-40) + z * ((-41) + z * ((-56) + z * ((-71) + z * ((-64) + z * ((-78) + z * ((-10) + z * ((-39) + z * ((-9) + z * (0 + z * (3 + z * (93 + z * (6 + z * (72 + z * ((-1) + z * ((-3) + z * (62 + z * (28 + z * (91 + z * (105 + z * (53 + z * ((-8) + z * ((-8) + z * (98 + z * (35 + z * (101 + z * (18 + z * (26 + z * ((-20) + z * ((-89) + z * (9 + z * ((-11) + z * ((-35) + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow2_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_64 z * u1 z = pow2_65_q z * f z + pow2_65 z + (131 : R) * pow2_65_mul_t z := by
  simp only [pow2_64, u1, pow2_65_q, f, pow2_65, pow2_65_mul_t]
  simp only [pow1_131]
  ring

theorem pow2_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_64 z * u1 z = pow2_65_q z * f z + pow2_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_65_mul_integer z


theorem pow2_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_64 z * u1 z = pow2_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_65_mul z


theorem pow2_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 65 = pow2_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow2_64_pow z hz]
  exact pow2_65_root z hz


def pow2_130 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (3 + z * (88 + z * (1 + z * (31 + z * (105 + z * (20 + z * (124 + z * (33 + z * (87 + z * (47 + z * (77 + z * (38 + z * (34 + z * (10 + z * (13 + z * (3 + z * (95 + z * (78 + z * 8)))))))))))))))))))

def pow2_130_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (118 + z * (78 + z * (103 + z * (27 + z * (40 + z * (42 + z * (92 + z * (127 + z * (64 + z * (88 + z * (97 + z * (19 + z * (41 + z * (35 + z * (116 + z * (9 + z * (74 + z * 105))))))))))))))))))

def pow2_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * ((-51) + z * (27 + z * ((-87) + z * (49 + z * ((-52) + z * (76 + z * (74 + z * (6 + z * (36 + z * (65 + z * (148 + z * ((-105) + z * (114 + z * (85 + z * (131 + z * (126 + z * (154 + z * (247 + z * (3 + z * (243 + z * (247 + z * (164 + z * (188 + z * (325 + z * (186 + z * ((-11) + z * (209 + z * (102 + z * (150 + z * (95 + z * (147 + z * (207 + z * (65 + z * (88 + z * (57 + z * (32 + z * (44 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow2_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_65 z * pow2_65 z = pow2_130_q z * f z + pow2_130 z + (131 : R) * pow2_130_mul_t z := by
  simp only [pow2_65, pow2_130_q, f, pow2_130, pow2_130_mul_t]
  
  ring

theorem pow2_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_65 z * pow2_65 z = pow2_130_q z * f z + pow2_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_130_mul_integer z


theorem pow2_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_65 z * pow2_65 z = pow2_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_130_mul z


theorem pow2_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 130 = pow2_130 z := by
  calc
    _ = u1 z ^ 65 * u1 z ^ 65 := by ring
    _ = pow2_65 z * pow2_65 z := by rw [pow2_65_pow z hz]
    _ = _ := pow2_130_root z hz


def pow2_131 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (111 + z * (70 + z * (108 + z * (52 + z * (26 + z * (95 + z * (93 + z * (75 + z * (108 + z * (35 + z * (42 + z * (64 + z * (23 + z * (90 + z * (49 + z * (55 + z * (90 + z * (129 + z * 129)))))))))))))))))))

def pow2_131_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (29 + z * (94 + z * (65 + z * (65 + z * (119 + z * (43 + z * (72 + z * (32 + z * (16 + z * (57 + z * (28 + z * (17 + z * (98 + z * (11 + z * (49 + z * (100 + z * (32 + z * 69))))))))))))))))))

def pow2_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (39 + z * (22 + z * (29 + z * ((-4) + z * (11 + z * (42 + z * ((-39) + z * (35 + z * ((-44) + z * (78 + z * ((-32) + z * (93 + z * (129 + z * ((-60) + z * (127 + z * ((-108) + z * (96 + z * (18 + z * ((-103) + z * (85 + z * ((-125) + z * ((-55) + z * (17 + z * ((-34) + z * ((-35) + z * ((-42) + z * ((-47) + z * ((-20) + z * ((-31) + z * ((-72) + z * ((-14) + z * ((-68) + z * ((-75) + z * ((-27) + z * ((-22) + z * ((-39) + z * ((-24) + z * ((-20) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow2_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_130 z * u1 z = pow2_131_q z * f z + pow2_131 z + (131 : R) * pow2_131_mul_t z := by
  simp only [pow2_130, u1, pow2_131_q, f, pow2_131, pow2_131_mul_t]
  simp only [pow1_131]
  ring

theorem pow2_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow2_130 z * u1 z = pow2_131_q z * f z + pow2_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow2_131_mul_integer z


theorem pow2_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow2_130 z * u1 z = pow2_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_131_mul z


theorem pow2_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u1 z ^ 131 = pow2_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow2_130_pow z hz]
  exact pow2_131_root z hz


abbrev u2 {R : Type*} [CommRing R] (z : R) : R := pow2_131 z

theorem iterate2 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 2) = u2 z := by
  calc
    _ = (z ^ (131 ^ 1)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u1 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate1 z hz)
    _ = _ := pow2_131_pow z hz

end DimensionTen.Mod131

end

end OAI
