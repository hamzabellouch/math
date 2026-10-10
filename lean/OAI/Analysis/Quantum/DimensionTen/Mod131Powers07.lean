import OAI.Analysis.Quantum.DimensionTen.Mod131Powers06

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow13_2 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (28 + z * (47 + z * (86 + z * (54 + z * (97 + z * (97 + z * (122 + z * (104 + z * (127 + z * (118 + z * (123 + z * (55 + z * (33 + z * (7 + z * (128 + z * (80 + z * (117 + z * (1 + z * 39)))))))))))))))))))

def pow13_2_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (39 + z * (23 + z * (41 + z * (63 + z * (59 + z * (77 + z * (78 + z * (7 + z * (58 + z * (2 + z * (74 + z * (3 + z * (48 + z * (34 + z * (90 + z * (22 + z * (68 + z * 112))))))))))))))))))

def pow13_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (48 + z * (52 + z * (63 + z * (97 + z * (23 + z * (48 + z * (45 + z * (61 + z * (17 + z * (26 + z * (162 + z * ((-1) + z * (89 + z * (64 + z * (8 + z * (105 + z * (72 + z * (133 + z * (44 + z * (166 + z * (141 + z * (79 + z * (6 + z * ((-2) + z * (170 + z * (53 + z * (34 + z * (135 + z * (123 + z * (61 + z * (6 + z * (46 + z * (137 + z * (42 + z * (59 + z * (64 + z * (81 + z * (20 + z * 48))))))))))))))))))))))))))))))))))))))

theorem pow13_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z + (131 : R) * pow13_2_mul_t z := by
  simp only [u12, pow13_2_q, f, pow13_2, pow13_2_mul_t]
  simp only [pow12_131]
  ring

theorem pow13_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_2_mul_integer z


theorem pow13_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z * u12 z = pow13_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_2_mul z


theorem pow13_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 2 = pow13_2 z := by
  calc
    _ = u12 z ^ 1 * u12 z ^ 1 := by ring
    _ = u12 z * u12 z := by simp only [pow_one]
    _ = _ := pow13_2_root z hz


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (130 + z * (34 + z * (25 + z * (120 + z * (18 + z * (63 + z * (92 + z * (91 + z * (70 + z * (64 + z * (118 + z * (58 + z * (17 + z * (45 + z * (112 + z * (46 + z * (52 + z * (75 + z * 37)))))))))))))))))))

def pow13_4_q {R : Type*} [CommRing R] (z : R) : R := (106 + z * (109 + z * (68 + z * (55 + z * (123 + z * (90 + z * (23 + z * (42 + z * (106 + z * (111 + z * (104 + z * (38 + z * (112 + z * (96 + z * (14 + z * (83 + z * (65 + z * (38 + z * 80))))))))))))))))))

def pow13_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * ((-46) + z * ((-53) + z * (9 + z * ((-57) + z * ((-64) + z * (12 + z * (95 + z * (62 + z * (71 + z * (215 + z * (261 + z * (150 + z * (148 + z * (265 + z * (368 + z * (293 + z * (287 + z * (349 + z * (327 + z * (205 + z * (203 + z * (369 + z * (189 + z * (284 + z * (247 + z * (280 + z * (174 + z * (75 + z * ((-93) + z * (50 + z * ((-25) + z * (153 + z * (32 + z * (44 + z * ((-31) + z * (14 + z * ((-40) + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow13_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z + (131 : R) * pow13_4_mul_t z := by
  simp only [pow13_2, pow13_4_q, f, pow13_4, pow13_4_mul_t]
  
  ring

theorem pow13_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_4_mul_integer z


theorem pow13_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_2 z * pow13_2 z = pow13_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_4_mul z


theorem pow13_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 4 = pow13_4 z := by
  calc
    _ = u12 z ^ 2 * u12 z ^ 2 := by ring
    _ = pow13_2 z * pow13_2 z := by rw [pow13_2_pow z hz]
    _ = _ := pow13_4_root z hz


def pow13_8 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (26 + z * (98 + z * (19 + z * (20 + z * (3 + z * (2 + z * (57 + z * (106 + z * (115 + z * (91 + z * (26 + z * (81 + z * (50 + z * (85 + z * (39 + z * (7 + z * (20 + z * (44 + z * 81)))))))))))))))))))

def pow13_8_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (106 + z * (9 + z * (99 + z * (96 + z * (50 + z * (85 + z * (92 + z * (121 + z * (60 + z * (42 + z * (69 + z * (38 + z * (86 + z * (26 + z * (120 + z * (55 + z * (84 + z * 59))))))))))))))))))

def pow13_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * (102 + z * (102 + z * ((-4) + z * (83 + z * (64 + z * ((-31) + z * (95 + z * (78 + z * (25 + z * (104 + z * (121 + z * (99 + z * ((-9) + z * ((-1) + z * (158 + z * (93 + z * ((-9) + z * (129 + z * (137 + z * ((-97) + z * (23 + z * (57 + z * (28 + z * ((-40) + z * (48 + z * (67 + z * (34 + z * ((-23) + z * (30 + z * (48 + z * ((-35) + z * (3 + z * (30 + z * ((-19) + z * ((-3) + z * (3 + z * (12 + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow13_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z + (131 : R) * pow13_8_mul_t z := by
  simp only [pow13_4, pow13_8_q, f, pow13_8, pow13_8_mul_t]
  
  ring

theorem pow13_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_8_mul_integer z


theorem pow13_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_4 z * pow13_4 z = pow13_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_8_mul z


theorem pow13_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 8 = pow13_8 z := by
  calc
    _ = u12 z ^ 4 * u12 z ^ 4 := by ring
    _ = pow13_4 z * pow13_4 z := by rw [pow13_4_pow z hz]
    _ = _ := pow13_8_root z hz


def pow13_16 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (23 + z * (5 + z * (108 + z * (16 + z * (61 + z * (37 + z * (112 + z * (92 + z * (91 + z * (47 + z * (22 + z * (34 + z * (106 + z * (96 + z * (126 + z * (19 + z * (1 + z * (17 + z * 3)))))))))))))))))))

def pow13_16_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (82 + z * (36 + z * (106 + z * (93 + z * (101 + z * (122 + z * (17 + z * (124 + z * (36 + z * (50 + z * (70 + z * (82 + z * (23 + z * (17 + z * (75 + z * (16 + z * (114 + z * 11))))))))))))))))))

def pow13_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (102 + z * (2 + z * (127 + z * ((-27) + z * ((-11) + z * ((-172) + z * ((-201) + z * ((-111) + z * ((-121) + z * (22 + z * (20 + z * ((-91) + z * ((-77) + z * ((-281) + z * ((-80) + z * ((-161) + z * ((-170) + z * ((-187) + z * ((-51) + z * ((-114) + z * ((-132) + z * ((-17) + z * ((-104) + z * ((-74) + z * ((-138) + z * ((-110) + z * (42 + z * (92 + z * (19 + z * (6 + z * ((-66) + z * (39 + z * (40 + z * (7 + z * ((-39) + z * ((-42) + z * ((-23) + z * (48 + z * 50))))))))))))))))))))))))))))))))))))))

theorem pow13_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z + (131 : R) * pow13_16_mul_t z := by
  simp only [pow13_8, pow13_16_q, f, pow13_16, pow13_16_mul_t]
  
  ring

theorem pow13_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_16_mul_integer z


theorem pow13_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_8 z * pow13_8 z = pow13_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_16_mul z


theorem pow13_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 16 = pow13_16 z := by
  calc
    _ = u12 z ^ 8 * u12 z ^ 8 := by ring
    _ = pow13_8 z * pow13_8 z := by rw [pow13_8_pow z hz]
    _ = _ := pow13_16_root z hz


def pow13_32 {R : Type*} [CommRing R] (z : R) : R := (64 + z * (110 + z * (86 + z * (19 + z * (107 + z * (103 + z * (101 + z * (85 + z * (37 + z * (116 + z * (38 + z * (48 + z * (56 + z * (15 + z * (62 + z * (62 + z * (28 + z * (12 + z * (119 + z * 108)))))))))))))))))))

def pow13_32_q {R : Type*} [CommRing R] (z : R) : R := (120 + z * (7 + z * (129 + z * (116 + z * (122 + z * (18 + z * (110 + z * (67 + z * (14 + z * (9 + z * (129 + z * (64 + z * (98 + z * (39 + z * (88 + z * (41 + z * (10 + z * (32 + z * 9))))))))))))))))))

def pow13_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-45) + z * ((-42) + z * ((-106) + z * ((-92) + z * ((-177) + z * ((-213) + z * ((-88) + z * ((-269) + z * ((-188) + z * ((-168) + z * ((-57) + z * ((-283) + z * ((-139) + z * ((-166) + z * ((-186) + z * ((-250) + z * (18 + z * ((-69) + z * ((-50) + z * ((-248) + z * (12 + z * (2 + z * (37 + z * ((-3) + z * (37 + z * ((-100) + z * ((-68) + z * (29 + z * (74 + z * (6 + z * ((-26) + z * ((-70) + z * ((-57) + z * ((-53) + z * ((-33) + z * ((-22) + z * ((-18) + z * ((-4) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow13_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_16 z * pow13_16 z = pow13_32_q z * f z + pow13_32 z + (131 : R) * pow13_32_mul_t z := by
  simp only [pow13_16, pow13_32_q, f, pow13_32, pow13_32_mul_t]
  
  ring

theorem pow13_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_16 z * pow13_16 z = pow13_32_q z * f z + pow13_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_32_mul_integer z


theorem pow13_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_16 z * pow13_16 z = pow13_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_32_mul z


theorem pow13_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 32 = pow13_32 z := by
  calc
    _ = u12 z ^ 16 * u12 z ^ 16 := by ring
    _ = pow13_16 z * pow13_16 z := by rw [pow13_16_pow z hz]
    _ = _ := pow13_32_root z hz


def pow13_64 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (74 + z * (18 + z * (46 + z * (17 + z * (48 + z * (121 + z * (77 + z * (114 + z * (12 + z * (111 + z * (85 + z * (98 + z * (100 + z * (81 + z * (58 + z * (47 + z * (116 + z * (67 + z * 46)))))))))))))))))))

def pow13_64_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (65 + z * (28 + z * (49 + z * (118 + z * (96 + z * (39 + z * (88 + z * (127 + z * (100 + z * (68 + z * (121 + z * (43 + z * (42 + z * (115 + z * (29 + z * (103 + z * (91 + z * 5))))))))))))))))))

def pow13_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * (43 + z * (89 + z * (83 + z * (46 + z * (67 + z * (225 + z * (193 + z * (87 + z * (86 + z * (216 + z * (129 + z * ((-60) + z * (12 + z * (65 + z * (8 + z * ((-113) + z * ((-146) + z * ((-47) + z * (23 + z * (118 + z * ((-75) + z * ((-111) + z * (104 + z * (60 + z * (0 + z * ((-55) + z * ((-54) + z * ((-2) + z * ((-66) + z * ((-3) + z * (17 + z * ((-23) + z * (49 + z * (55 + z * ((-27) + z * (79 + z * (193 + z * 89))))))))))))))))))))))))))))))))))))))

theorem pow13_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_32 z * pow13_32 z = pow13_64_q z * f z + pow13_64 z + (131 : R) * pow13_64_mul_t z := by
  simp only [pow13_32, pow13_64_q, f, pow13_64, pow13_64_mul_t]
  
  ring

theorem pow13_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_32 z * pow13_32 z = pow13_64_q z * f z + pow13_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_64_mul_integer z


theorem pow13_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_32 z * pow13_32 z = pow13_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_64_mul z


theorem pow13_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 64 = pow13_64 z := by
  calc
    _ = u12 z ^ 32 * u12 z ^ 32 := by ring
    _ = pow13_32 z * pow13_32 z := by rw [pow13_32_pow z hz]
    _ = _ := pow13_64_root z hz


def pow13_65 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (28 + z * (110 + z * (128 + z * (119 + z * (129 + z * (120 + z * (77 + z * (5 + z * (49 + z * (3 + z * (18 + z * (70 + z * (55 + z * (130 + z * (88 + z * (34 + z * (56 + z * (113 + z * 115)))))))))))))))))))

def pow13_65_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (127 + z * (51 + z * (90 + z * (96 + z * (5 + z * (107 + z * (50 + z * (71 + z * (114 + z * (65 + z * (3 + z * (45 + z * (13 + z * (128 + z * (12 + z * (18 + z * (130 + z * 12))))))))))))))))))

def pow13_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (1 + z * ((-36) + z * ((-16) + z * ((-90) + z * ((-131) + z * ((-34) + z * ((-1) + z * ((-107) + z * ((-112) + z * (29 + z * ((-98) + z * ((-95) + z * (28 + z * ((-108) + z * (65 + z * (32 + z * (34 + z * (89 + z * ((-32) + z * (157 + z * (27 + z * (8 + z * (249 + z * (239 + z * (72 + z * (127 + z * (237 + z * (121 + z * (182 + z * (132 + z * (199 + z * (152 + z * (35 + z * (127 + z * (81 + z * (71 + z * (56 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow13_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_64 z * u12 z = pow13_65_q z * f z + pow13_65 z + (131 : R) * pow13_65_mul_t z := by
  simp only [pow13_64, u12, pow13_65_q, f, pow13_65, pow13_65_mul_t]
  simp only [pow12_131]
  ring

theorem pow13_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_64 z * u12 z = pow13_65_q z * f z + pow13_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_65_mul_integer z


theorem pow13_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_64 z * u12 z = pow13_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_65_mul z


theorem pow13_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 65 = pow13_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow13_64_pow z hz]
  exact pow13_65_root z hz


def pow13_130 {R : Type*} [CommRing R] (z : R) : R := (111 + z * (107 + z * (77 + z * (19 + z * (116 + z * (85 + z * (1 + z * (25 + z * (86 + z * (6 + z * (54 + z * (99 + z * (56 + z * (92 + z * (93 + z * (31 + z * (0 + z * (34 + z * (105 + z * 111)))))))))))))))))))

def pow13_130_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (32 + z * (126 + z * (71 + z * (75 + z * (43 + z * (102 + z * (91 + z * (45 + z * (82 + z * (99 + z * (116 + z * (96 + z * (17 + z * (83 + z * (116 + z * (103 + z * (55 + z * 125))))))))))))))))))

def pow13_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-40) + z * ((-46) + z * ((-87) + z * ((-38) + z * ((-12) + z * (78 + z * (199 + z * (203 + z * (286 + z * (274 + z * (165 + z * ((-38) + z * ((-78) + z * ((-207) + z * ((-200) + z * ((-175) + z * ((-26) + z * (72 + z * (69 + z * (70 + z * (211 + z * (346 + z * (104 + z * (19 + z * (152 + z * ((-33) + z * ((-125) + z * ((-167) + z * ((-56) + z * ((-87) + z * (11 + z * (105 + z * (225 + z * (205 + z * (29 + z * (32 + z * (111 + z * (135 + z * 100))))))))))))))))))))))))))))))))))))))

theorem pow13_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_65 z * pow13_65 z = pow13_130_q z * f z + pow13_130 z + (131 : R) * pow13_130_mul_t z := by
  simp only [pow13_65, pow13_130_q, f, pow13_130, pow13_130_mul_t]
  
  ring

theorem pow13_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_65 z * pow13_65 z = pow13_130_q z * f z + pow13_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_130_mul_integer z


theorem pow13_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_65 z * pow13_65 z = pow13_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_130_mul z


theorem pow13_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 130 = pow13_130 z := by
  calc
    _ = u12 z ^ 65 * u12 z ^ 65 := by ring
    _ = pow13_65 z * pow13_65 z := by rw [pow13_65_pow z hz]
    _ = _ := pow13_130_root z hz


def pow13_131 {R : Type*} [CommRing R] (z : R) : R := (111 + z * (37 + z * (126 + z * (77 + z * (12 + z * (1 + z * (66 + z * (12 + z * (82 + z * (36 + z * (87 + z * (127 + z * (122 + z * (1 + z * (103 + z * (126 + z * (17 + z * (80 + z * (78 + z * 56)))))))))))))))))))

def pow13_131_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (130 + z * (60 + z * (92 + z * (38 + z * (65 + z * (128 + z * (107 + z * (53 + z * (48 + z * (75 + z * (90 + z * (7 + z * (103 + z * (98 + z * (100 + z * (81 + z * (80 + z * 103))))))))))))))))))

def pow13_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (66 + z * (63 + z * (65 + z * (29 + z * (72 + z * (42 + z * ((-48) + z * (31 + z * ((-84) + z * ((-76) + z * ((-8) + z * ((-11) + z * ((-136) + z * ((-69) + z * ((-61) + z * ((-101) + z * ((-156) + z * ((-80) + z * ((-161) + z * ((-92) + z * ((-61) + z * ((-43) + z * ((-231) + z * ((-118) + z * ((-74) + z * ((-156) + z * ((-193) + z * ((-49) + z * (62 + z * ((-37) + z * ((-32) + z * (14 + z * (21 + z * ((-29) + z * ((-50) + z * (18 + z * (78 + z * (65 + z * 67))))))))))))))))))))))))))))))))))))))

theorem pow13_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_130 z * u12 z = pow13_131_q z * f z + pow13_131 z + (131 : R) * pow13_131_mul_t z := by
  simp only [pow13_130, u12, pow13_131_q, f, pow13_131, pow13_131_mul_t]
  simp only [pow12_131]
  ring

theorem pow13_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow13_130 z * u12 z = pow13_131_q z * f z + pow13_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow13_131_mul_integer z


theorem pow13_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow13_130 z * u12 z = pow13_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_131_mul z


theorem pow13_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u12 z ^ 131 = pow13_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow13_130_pow z hz]
  exact pow13_131_root z hz


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_131 z

theorem iterate13 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 13) = u13 z := by
  calc
    _ = (z ^ (131 ^ 12)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate12 z hz)
    _ = _ := pow13_131_pow z hz


def pow14_2 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (74 + z * (7 + z * (19 + z * (107 + z * (84 + z * (51 + z * (79 + z * (53 + z * (83 + z * (19 + z * (125 + z * (125 + z * (108 + z * (89 + z * (65 + z * (114 + z * (81 + z * (57 + z * 88)))))))))))))))))))

def pow14_2_q {R : Type*} [CommRing R] (z : R) : R := (58 + z * (124 + z * (71 + z * (61 + z * (64 + z * (63 + z * (114 + z * (22 + z * (80 + z * (65 + z * (61 + z * (76 + z * (20 + z * (1 + z * (66 + z * (120 + z * (11 + z * (94 + z * 123))))))))))))))))))

def pow14_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * ((-6) + z * (124 + z * (82 + z * (50 + z * ((-51) + z * ((-75) + z * ((-146) + z * ((-30) + z * ((-124) + z * ((-1) + z * (46 + z * (131 + z * ((-45) + z * (210 + z * (48 + z * ((-19) + z * (146 + z * (103 + z * ((-75) + z * (116 + z * (153 + z * ((-44) + z * (67 + z * (94 + z * (159 + z * (192 + z * (151 + z * (121 + z * (298 + z * (142 + z * (69 + z * (164 + z * (71 + z * ((-5) + z * (15 + z * (12 + z * (4 + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow14_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z + (131 : R) * pow14_2_mul_t z := by
  simp only [u13, pow14_2_q, f, pow14_2, pow14_2_mul_t]
  simp only [pow13_131]
  ring

theorem pow14_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_2_mul_integer z


theorem pow14_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z * u13 z = pow14_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_2_mul z


theorem pow14_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 2 = pow14_2 z := by
  calc
    _ = u13 z ^ 1 * u13 z ^ 1 := by ring
    _ = u13 z * u13 z := by simp only [pow_one]
    _ = _ := pow14_2_root z hz


def pow14_4 {R : Type*} [CommRing R] (z : R) : R := (79 + z * (71 + z * (100 + z * (55 + z * (76 + z * (35 + z * (83 + z * (114 + z * (122 + z * (115 + z * (23 + z * (75 + z * (81 + z * (120 + z * (127 + z * (42 + z * (37 + z * (109 + z * (106 + z * 62)))))))))))))))))))

def pow14_4_q {R : Type*} [CommRing R] (z : R) : R := (48 + z * (65 + z * (126 + z * (5 + z * (114 + z * (105 + z * (84 + z * (63 + z * (37 + z * (44 + z * (70 + z * (118 + z * (120 + z * (51 + z * (128 + z * (1 + z * (47 + z * (3 + z * 15))))))))))))))))))

def pow14_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (91 + z * (93 + z * ((-41) + z * ((-45) + z * (73 + z * (94 + z * ((-50) + z * ((-23) + z * (67 + z * (3 + z * ((-48) + z * (94 + z * (147 + z * (78 + z * (54 + z * (95 + z * (250 + z * (258 + z * (233 + z * (266 + z * (347 + z * (210 + z * (263 + z * (340 + z * (378 + z * (355 + z * (387 + z * (352 + z * (434 + z * (319 + z * (366 + z * (330 + z * (285 + z * (228 + z * (203 + z * (193 + z * (125 + z * (69 + z * 59))))))))))))))))))))))))))))))))))))))

theorem pow14_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z + (131 : R) * pow14_4_mul_t z := by
  simp only [pow14_2, pow14_4_q, f, pow14_4, pow14_4_mul_t]
  
  ring

theorem pow14_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_4_mul_integer z


theorem pow14_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_2 z * pow14_2 z = pow14_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_4_mul z


theorem pow14_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 4 = pow14_4 z := by
  calc
    _ = u13 z ^ 2 * u13 z ^ 2 := by ring
    _ = pow14_2 z * pow14_2 z := by rw [pow14_2_pow z hz]
    _ = _ := pow14_4_root z hz


def pow14_8 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (60 + z * (91 + z * (4 + z * (8 + z * (85 + z * (54 + z * (49 + z * (26 + z * (73 + z * (100 + z * (33 + z * (65 + z * (88 + z * (85 + z * (11 + z * (127 + z * (20 + z * (49 + z * 41)))))))))))))))))))

def pow14_8_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (87 + z * (89 + z * (94 + z * (4 + z * (97 + z * (100 + z * (6 + z * (23 + z * (129 + z * (57 + z * (38 + z * (30 + z * (37 + z * (67 + z * (63 + z * (111 + z * (87 + z * 45))))))))))))))))))

def pow14_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * (43 + z * (81 + z * (60 + z * (120 + z * (39 + z * (61 + z * (115 + z * (243 + z * (295 + z * (163 + z * (232 + z * (272 + z * (274 + z * (294 + z * (554 + z * (415 + z * (322 + z * (367 + z * (484 + z * (536 + z * (433 + z * (365 + z * (401 + z * (340 + z * (429 + z * (507 + z * (332 + z * (186 + z * (161 + z * (292 + z * (345 + z * (227 + z * (76 + z * (46 + z * (99 + z * (124 + z * (77 + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow14_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z + (131 : R) * pow14_8_mul_t z := by
  simp only [pow14_4, pow14_8_q, f, pow14_8, pow14_8_mul_t]
  
  ring

theorem pow14_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_8_mul_integer z


theorem pow14_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_4 z * pow14_4 z = pow14_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_8_mul z


theorem pow14_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 8 = pow14_8 z := by
  calc
    _ = u13 z ^ 4 * u13 z ^ 4 := by ring
    _ = pow14_4 z * pow14_4 z := by rw [pow14_4_pow z hz]
    _ = _ := pow14_8_root z hz


def pow14_16 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (1 + z * (48 + z * (37 + z * (50 + z * (16 + z * (45 + z * (85 + z * (87 + z * (106 + z * (28 + z * (82 + z * (22 + z * (19 + z * (98 + z * (17 + z * (72 + z * (97 + z * (98 + z * 108)))))))))))))))))))

def pow14_16_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (60 + z * (41 + z * (52 + z * (73 + z * (48 + z * (97 + z * (116 + z * (3 + z * (64 + z * (82 + z * (34 + z * (122 + z * (127 + z * (129 + z * (21 + z * (115 + z * (99 + z * 109))))))))))))))))))

def pow14_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-11) + z * (8 + z * (20 + z * ((-9) + z * ((-80) + z * ((-74) + z * ((-3) + z * ((-86) + z * ((-138) + z * ((-68) + z * ((-49) + z * ((-100) + z * ((-151) + z * ((-198) + z * ((-71) + z * ((-119) + z * ((-244) + z * ((-201) + z * ((-156) + z * ((-189) + z * ((-189) + z * ((-233) + z * ((-151) + z * ((-138) + z * ((-255) + z * ((-55) + z * ((-84) + z * ((-67) + z * ((-160) + z * ((-84) + z * ((-129) + z * (5 + z * ((-114) + z * ((-67) + z * ((-49) + z * ((-69) + z * ((-25) + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow14_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z + (131 : R) * pow14_16_mul_t z := by
  simp only [pow14_8, pow14_16_q, f, pow14_16, pow14_16_mul_t]
  
  ring

theorem pow14_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_16_mul_integer z


theorem pow14_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_8 z * pow14_8 z = pow14_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_16_mul z


theorem pow14_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 16 = pow14_16 z := by
  calc
    _ = u13 z ^ 8 * u13 z ^ 8 := by ring
    _ = pow14_8 z * pow14_8 z := by rw [pow14_8_pow z hz]
    _ = _ := pow14_16_root z hz


def pow14_32 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (113 + z * (15 + z * (82 + z * (34 + z * (106 + z * (75 + z * (109 + z * (23 + z * (43 + z * (48 + z * (90 + z * (85 + z * (112 + z * (106 + z * (120 + z * (89 + z * (13 + z * (0 + z * 18)))))))))))))))))))

def pow14_32_q {R : Type*} [CommRing R] (z : R) : R := (63 + z * (92 + z * (68 + z * (100 + z * (38 + z * (129 + z * (88 + z * (64 + z * (121 + z * (74 + z * (104 + z * (7 + z * (58 + z * (42 + z * (113 + z * (25 + z * (61 + z * (9 + z * 5))))))))))))))))))

def pow14_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-58) + z * ((-62) + z * ((-97) + z * ((-87) + z * ((-192) + z * ((-161) + z * ((-185) + z * ((-228) + z * ((-193) + z * ((-283) + z * ((-153) + z * ((-285) + z * ((-289) + z * ((-279) + z * ((-212) + z * ((-197) + z * ((-215) + z * ((-150) + z * ((-192) + z * ((-59) + z * ((-134) + z * (1 + z * (67 + z * (22 + z * (186 + z * (191 + z * (171 + z * (234 + z * (63 + z * (167 + z * (101 + z * (118 + z * (195 + z * (160 + z * (227 + z * (226 + z * (159 + z * 89))))))))))))))))))))))))))))))))))))))

theorem pow14_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_16 z * pow14_16 z = pow14_32_q z * f z + pow14_32 z + (131 : R) * pow14_32_mul_t z := by
  simp only [pow14_16, pow14_32_q, f, pow14_32, pow14_32_mul_t]
  
  ring

theorem pow14_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_16 z * pow14_16 z = pow14_32_q z * f z + pow14_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_32_mul_integer z


theorem pow14_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_16 z * pow14_16 z = pow14_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_32_mul z


theorem pow14_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 32 = pow14_32 z := by
  calc
    _ = u13 z ^ 16 * u13 z ^ 16 := by ring
    _ = pow14_16 z * pow14_16 z := by rw [pow14_16_pow z hz]
    _ = _ := pow14_32_root z hz


def pow14_64 {R : Type*} [CommRing R] (z : R) : R := (129 + z * (42 + z * (73 + z * (71 + z * (52 + z * (69 + z * (105 + z * (9 + z * (0 + z * (128 + z * (91 + z * (19 + z * (3 + z * (9 + z * (113 + z * (78 + z * (27 + z * (98 + z * (96 + z * 7)))))))))))))))))))

def pow14_64_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (122 + z * (42 + z * (113 + z * (41 + z * (113 + z * (96 + z * (123 + z * (40 + z * (72 + z * (80 + z * (70 + z * (74 + z * (113 + z * (13 + z * (78 + z * (35 + z * (100 + z * 62))))))))))))))))))

def pow14_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (105 + z * (156 + z * (42 + z * (59 + z * (84 + z * (54 + z * (141 + z * (139 + z * (41 + z * ((-57) + z * (36 + z * (40 + z * (98 + z * (122 + z * (150 + z * (225 + z * (301 + z * (85 + z * (9 + z * (89 + z * (62 + z * (63 + z * ((-23) + z * ((-33) + z * ((-54) + z * (7 + z * (81 + z * (191 + z * (91 + z * (54 + z * (58 + z * (11 + z * ((-32) + z * ((-92) + z * ((-99) + z * ((-62) + z * ((-75) + z * ((-32) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow14_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_32 z * pow14_32 z = pow14_64_q z * f z + pow14_64 z + (131 : R) * pow14_64_mul_t z := by
  simp only [pow14_32, pow14_64_q, f, pow14_64, pow14_64_mul_t]
  
  ring

theorem pow14_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_32 z * pow14_32 z = pow14_64_q z * f z + pow14_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_64_mul_integer z


theorem pow14_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_32 z * pow14_32 z = pow14_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_64_mul z


theorem pow14_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 64 = pow14_64 z := by
  calc
    _ = u13 z ^ 32 * u13 z ^ 32 := by ring
    _ = pow14_32 z * pow14_32 z := by rw [pow14_32_pow z hz]
    _ = _ := pow14_64_root z hz


def pow14_65 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (65 + z * (64 + z * (59 + z * (64 + z * (103 + z * (88 + z * (127 + z * (118 + z * (114 + z * (58 + z * (94 + z * (14 + z * (92 + z * (123 + z * (90 + z * (37 + z * (53 + z * (88 + z * 10)))))))))))))))))))

def pow14_65_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (29 + z * (16 + z * (72 + z * (52 + z * (56 + z * (32 + z * (27 + z * (22 + z * (111 + z * (49 + z * (57 + z * (91 + z * (5 + z * (112 + z * (125 + z * (121 + z * (93 + z * 130))))))))))))))))))

def pow14_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (102 + z * (54 + z * (172 + z * (146 + z * (102 + z * (79 + z * (167 + z * (52 + z * (106 + z * (105 + z * (98 + z * (173 + z * (218 + z * (36 + z * (96 + z * (186 + z * (35 + z * (218 + z * (137 + z * ((-29) + z * (78 + z * (46 + z * ((-238) + z * ((-172) + z * (66 + z * ((-69) + z * ((-57) + z * ((-123) + z * ((-13) + z * (39 + z * ((-103) + z * ((-92) + z * (79 + z * ((-34) + z * ((-110) + z * ((-23) + z * ((-3) + z * ((-21) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow14_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_64 z * u13 z = pow14_65_q z * f z + pow14_65 z + (131 : R) * pow14_65_mul_t z := by
  simp only [pow14_64, u13, pow14_65_q, f, pow14_65, pow14_65_mul_t]
  simp only [pow13_131]
  ring

theorem pow14_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_64 z * u13 z = pow14_65_q z * f z + pow14_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_65_mul_integer z


theorem pow14_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_64 z * u13 z = pow14_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_65_mul z


theorem pow14_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 65 = pow14_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow14_64_pow z hz]
  exact pow14_65_root z hz


def pow14_130 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (83 + z * (59 + z * (41 + z * (100 + z * (122 + z * (87 + z * (73 + z * (63 + z * (123 + z * (54 + z * (0 + z * (14 + z * (103 + z * (27 + z * (78 + z * (93 + z * (58 + z * (71 + z * 56)))))))))))))))))))

def pow14_130_q {R : Type*} [CommRing R] (z : R) : R := (120 + z * (94 + z * (3 + z * (127 + z * (45 + z * (78 + z * (125 + z * (15 + z * (69 + z * (58 + z * (81 + z * (32 + z * (56 + z * (75 + z * (40 + z * (128 + z * (84 + z * (7 + z * 100))))))))))))))))))

def pow14_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-23) + z * ((-6) + z * ((-2) + z * ((-1) + z * ((-54) + z * (62 + z * (122 + z * (55 + z * (237 + z * (211 + z * (179 + z * (214 + z * (239 + z * (326 + z * (396 + z * (336 + z * (225 + z * (342 + z * (280 + z * (305 + z * (316 + z * (347 + z * (257 + z * (286 + z * (234 + z * (123 + z * (108 + z * (134 + z * (81 + z * (33 + z * (32 + z * (96 + z * (27 + z * ((-86) + z * ((-7) + z * (18 + z * ((-37) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow14_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_65 z * pow14_65 z = pow14_130_q z * f z + pow14_130 z + (131 : R) * pow14_130_mul_t z := by
  simp only [pow14_65, pow14_130_q, f, pow14_130, pow14_130_mul_t]
  
  ring

theorem pow14_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_65 z * pow14_65 z = pow14_130_q z * f z + pow14_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_130_mul_integer z


theorem pow14_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_65 z * pow14_65 z = pow14_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_130_mul z


theorem pow14_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 130 = pow14_130 z := by
  calc
    _ = u13 z ^ 65 * u13 z ^ 65 := by ring
    _ = pow14_65 z * pow14_65 z := by rw [pow14_65_pow z hz]
    _ = _ := pow14_130_root z hz


def pow14_131 {R : Type*} [CommRing R] (z : R) : R := (93 + z * (91 + z * (41 + z * (95 + z * (97 + z * (39 + z * (42 + z * (96 + z * (8 + z * (19 + z * (113 + z * (59 + z * (50 + z * (1 + z * (39 + z * (105 + z * (104 + z * (74 + z * (71 + z * 23)))))))))))))))))))

def pow14_131_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (72 + z * (35 + z * (15 + z * (91 + z * (7 + z * (128 + z * (75 + z * (93 + z * (14 + z * (74 + z * (126 + z * (25 + z * (43 + z * (88 + z * (81 + z * (1 + z * (95 + z * 123))))))))))))))))))

def pow14_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * (40 + z * (31 + z * (76 + z * (128 + z * (120 + z * (54 + z * (171 + z * (44 + z * (76 + z * (72 + z * (6 + z * (28 + z * (61 + z * ((-9) + z * (102 + z * (251 + z * (153 + z * (122 + z * (103 + z * (172 + z * (232 + z * ((-128) + z * ((-16) + z * (184 + z * (18 + z * ((-68) + z * (142 + z * (143 + z * ((-39) + z * (36 + z * (85 + z * (106 + z * (56 + z * (29 + z * (35 + z * ((-2) + z * (1 + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow14_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_130 z * u13 z = pow14_131_q z * f z + pow14_131 z + (131 : R) * pow14_131_mul_t z := by
  simp only [pow14_130, u13, pow14_131_q, f, pow14_131, pow14_131_mul_t]
  simp only [pow13_131]
  ring

theorem pow14_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow14_130 z * u13 z = pow14_131_q z * f z + pow14_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow14_131_mul_integer z


theorem pow14_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow14_130 z * u13 z = pow14_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_131_mul z


theorem pow14_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u13 z ^ 131 = pow14_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow14_130_pow z hz]
  exact pow14_131_root z hz


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_131 z

theorem iterate14 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 14) = u14 z := by
  calc
    _ = (z ^ (131 ^ 13)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate13 z hz)
    _ = _ := pow14_131_pow z hz

end DimensionTen.Mod131

end

end OAI
