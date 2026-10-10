import OAI.Analysis.Quantum.DimensionTen.Mod131Powers03

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (22 + z * (112 + z * (71 + z * (126 + z * (110 + z * (67 + z * (24 + z * (63 + z * (59 + z * (23 + z * (80 + z * (106 + z * (120 + z * (29 + z * (83 + z * (101 + z * (24 + z * (80 + z * 55)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (129 + z * (70 + z * (35 + z * (22 + z * (79 + z * (117 + z * (115 + z * (8 + z * (23 + z * (112 + z * (12 + z * (13 + z * (7 + z * (38 + z * (62 + z * (114 + z * (3 + z * 80))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (28 + z * (71 + z * (130 + z * (146 + z * (167 + z * (95 + z * (72 + z * (214 + z * (326 + z * (343 + z * (373 + z * (432 + z * (454 + z * (607 + z * (616 + z * (614 + z * (709 + z * (735 + z * (783 + z * (900 + z * (868 + z * (698 + z * (677 + z * (631 + z * (821 + z * (722 + z * (659 + z * (561 + z * (538 + z * (481 + z * (529 + z * (318 + z * (241 + z * (205 + z * (192 + z * (183 + z * (117 + z * (21 + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow7_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z + (131 : R) * pow7_2_mul_t z := by
  simp only [u6, pow7_2_q, f, pow7_2, pow7_2_mul_t]
  simp only [pow6_131]
  ring

theorem pow7_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_2_mul_integer z


theorem pow7_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z * u6 z = pow7_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_2_mul z


theorem pow7_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 2 = pow7_2 z := by
  calc
    _ = u6 z ^ 1 * u6 z ^ 1 := by ring
    _ = u6 z * u6 z := by simp only [pow_one]
    _ = _ := pow7_2_root z hz


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (124 + z * (65 + z * (50 + z * (19 + z * (35 + z * (82 + z * (107 + z * (19 + z * (69 + z * (107 + z * (94 + z * (24 + z * (35 + z * (95 + z * (82 + z * (54 + z * (0 + z * (70 + z * 89)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (71 + z * (112 + z * (121 + z * (121 + z * (112 + z * (40 + z * (48 + z * (88 + z * (30 + z * (57 + z * (7 + z * (61 + z * (13 + z * (121 + z * (96 + z * (60 + z * (5 + z * (17 + z * 12))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * ((-47) + z * ((-5) + z * ((-48) + z * (43 + z * (16 + z * (85 + z * (70 + z * (71 + z * (21 + z * (69 + z * ((-13) + z * ((-19) + z * (82 + z * (28 + z * (147 + z * (211 + z * (309 + z * (222 + z * (148 + z * (235 + z * (294 + z * (154 + z * (247 + z * (284 + z * (140 + z * (107 + z * (243 + z * (271 + z * (207 + z * (158 + z * (228 + z * (109 + z * (70 + z * (150 + z * (99 + z * (55 + z * (61 + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow7_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z + (131 : R) * pow7_4_mul_t z := by
  simp only [pow7_2, pow7_4_q, f, pow7_4, pow7_4_mul_t]
  
  ring

theorem pow7_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_4_mul_integer z


theorem pow7_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_2 z * pow7_2 z = pow7_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_4_mul z


theorem pow7_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 4 = pow7_4 z := by
  calc
    _ = u6 z ^ 2 * u6 z ^ 2 := by ring
    _ = pow7_2 z * pow7_2 z := by rw [pow7_2_pow z hz]
    _ = _ := pow7_4_root z hz


def pow7_8 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (82 + z * (32 + z * (95 + z * (95 + z * (98 + z * (14 + z * (105 + z * (2 + z * (5 + z * (50 + z * (94 + z * (115 + z * (75 + z * (48 + z * (33 + z * (82 + z * (72 + z * (19 + z * 31)))))))))))))))))))

def pow7_8_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (49 + z * (58 + z * (24 + z * (8 + z * (81 + z * (101 + z * (83 + z * (80 + z * (62 + z * (103 + z * (59 + z * (123 + z * (22 + z * (80 + z * (22 + z * (97 + z * (50 + z * 61))))))))))))))))))

def pow7_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * (11 + z * (87 + z * (80 + z * (72 + z * ((-5) + z * ((-21) + z * (52 + z * (127 + z * ((-3) + z * ((-24) + z * (79 + z * (87 + z * ((-27) + z * ((-95) + z * (44 + z * (128 + z * (42 + z * ((-128) + z * ((-69) + z * (163 + z * (69 + z * ((-11) + z * ((-158) + z * ((-1) + z * (103 + z * (59 + z * ((-103) + z * (21 + z * (87 + z * (56 + z * ((-45) + z * (34 + z * (80 + z * (55 + z * ((-21) + z * ((-16) + z * (64 + z * 60))))))))))))))))))))))))))))))))))))))

theorem pow7_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z + (131 : R) * pow7_8_mul_t z := by
  simp only [pow7_4, pow7_8_q, f, pow7_8, pow7_8_mul_t]
  
  ring

theorem pow7_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_8_mul_integer z


theorem pow7_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_4 z * pow7_4 z = pow7_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_8_mul z


theorem pow7_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 8 = pow7_8 z := by
  calc
    _ = u6 z ^ 4 * u6 z ^ 4 := by ring
    _ = pow7_4 z * pow7_4 z := by rw [pow7_4_pow z hz]
    _ = _ := pow7_8_root z hz


def pow7_16 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (114 + z * (125 + z * (112 + z * (78 + z * (70 + z * (19 + z * (46 + z * (48 + z * (124 + z * (42 + z * (122 + z * (29 + z * (38 + z * (91 + z * (18 + z * (65 + z * (48 + z * (71 + z * 68)))))))))))))))))))

def pow7_16_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (130 + z * (67 + z * (17 + z * (75 + z * (28 + z * (47 + z * (30 + z * (98 + z * (12 + z * (46 + z * (28 + z * (117 + z * (46 + z * (94 + z * (104 + z * (79 + z * (108 + z * 44))))))))))))))))))

def pow7_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-47) + z * ((-88) + z * ((-79) + z * ((-69) + z * ((-23) + z * ((-62) + z * (20 + z * (21 + z * (54 + z * ((-113) + z * (1 + z * ((-66) + z * ((-122) + z * ((-168) + z * (88 + z * (53 + z * ((-8) + z * ((-22) + z * (35 + z * ((-132) + z * ((-80) + z * ((-47) + z * ((-27) + z * ((-24) + z * ((-8) + z * ((-159) + z * ((-84) + z * ((-63) + z * ((-27) + z * ((-2) + z * ((-43) + z * ((-67) + z * ((-53) + z * ((-85) + z * ((-79) + z * ((-46) + z * ((-38) + z * ((-14) + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow7_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z + (131 : R) * pow7_16_mul_t z := by
  simp only [pow7_8, pow7_16_q, f, pow7_16, pow7_16_mul_t]
  
  ring

theorem pow7_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_16_mul_integer z


theorem pow7_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_8 z * pow7_8 z = pow7_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_16_mul z


theorem pow7_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 16 = pow7_16 z := by
  calc
    _ = u6 z ^ 8 * u6 z ^ 8 := by ring
    _ = pow7_8 z * pow7_8 z := by rw [pow7_8_pow z hz]
    _ = _ := pow7_16_root z hz


def pow7_32 {R : Type*} [CommRing R] (z : R) : R := (58 + z * (49 + z * (70 + z * (95 + z * (57 + z * (114 + z * (12 + z * (8 + z * (75 + z * (101 + z * (106 + z * (12 + z * (34 + z * (93 + z * (106 + z * (26 + z * (36 + z * (130 + z * (66 + z * 130)))))))))))))))))))

def pow7_32_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (90 + z * (10 + z * (96 + z * (79 + z * (25 + z * (1 + z * (100 + z * (52 + z * (29 + z * (81 + z * (60 + z * (104 + z * (37 + z * (42 + z * (126 + z * (94 + z * (8 + z * 39))))))))))))))))))

def pow7_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (36 + z * (94 + z * (200 + z * (266 + z * (305 + z * (267 + z * (241 + z * (210 + z * (77 + z * (189 + z * (289 + z * (323 + z * (209 + z * (302 + z * (274 + z * (98 + z * (137 + z * (132 + z * (270 + z * (189 + z * (172 + z * (190 + z * (149 + z * ((-35) + z * ((-23) + z * (111 + z * ((-49) + z * (49 + z * (64 + z * (15 + z * (89 + z * ((-62) + z * (32 + z * (32 + z * ((-28) + z * (53 + z * (66 + z * (54 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow7_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_16 z * pow7_16 z = pow7_32_q z * f z + pow7_32 z + (131 : R) * pow7_32_mul_t z := by
  simp only [pow7_16, pow7_32_q, f, pow7_32, pow7_32_mul_t]
  
  ring

theorem pow7_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_16 z * pow7_16 z = pow7_32_q z * f z + pow7_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_32_mul_integer z


theorem pow7_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_16 z * pow7_16 z = pow7_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_32_mul z


theorem pow7_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 32 = pow7_32 z := by
  calc
    _ = u6 z ^ 16 * u6 z ^ 16 := by ring
    _ = pow7_16 z * pow7_16 z := by rw [pow7_16_pow z hz]
    _ = _ := pow7_32_root z hz


def pow7_64 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (128 + z * (25 + z * (113 + z * (24 + z * (69 + z * (31 + z * (8 + z * (112 + z * (25 + z * (51 + z * (72 + z * (59 + z * (81 + z * (23 + z * (93 + z * (1 + z * (95 + z * (69 + z * 29)))))))))))))))))))

def pow7_64_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (74 + z * (112 + z * (102 + z * (72 + z * (65 + z * (105 + z * (42 + z * (117 + z * (72 + z * (69 + z * (110 + z * (53 + z * (2 + z * (37 + z * (60 + z * (75 + z * (64 + z * 1))))))))))))))))))

def pow7_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * ((-7) + z * ((-18) + z * (10 + z * ((-5) + z * (33 + z * ((-17) + z * ((-63) + z * ((-62) + z * ((-78) + z * ((-39) + z * ((-128) + z * ((-79) + z * ((-64) + z * ((-11) + z * ((-57) + z * ((-158) + z * (27 + z * (139 + z * (113 + z * (44 + z * (67 + z * (297 + z * (174 + z * (114 + z * (4 + z * (180 + z * (291 + z * (185 + z * (177 + z * (142 + z * (279 + z * (245 + z * (192 + z * (128 + z * (135 + z * (258 + z * (130 + z * 129))))))))))))))))))))))))))))))))))))))

theorem pow7_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_32 z * pow7_32 z = pow7_64_q z * f z + pow7_64 z + (131 : R) * pow7_64_mul_t z := by
  simp only [pow7_32, pow7_64_q, f, pow7_64, pow7_64_mul_t]
  
  ring

theorem pow7_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_32 z * pow7_32 z = pow7_64_q z * f z + pow7_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_64_mul_integer z


theorem pow7_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_32 z * pow7_32 z = pow7_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_64_mul z


theorem pow7_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 64 = pow7_64 z := by
  calc
    _ = u6 z ^ 32 * u6 z ^ 32 := by ring
    _ = pow7_32 z * pow7_32 z := by rw [pow7_32_pow z hz]
    _ = _ := pow7_64_root z hz


def pow7_65 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (51 + z * (61 + z * (125 + z * (7 + z * (47 + z * (129 + z * (113 + z * (120 + z * (125 + z * (114 + z * (92 + z * (128 + z * (99 + z * (72 + z * (60 + z * (2 + z * (92 + z * (17 + z * 90)))))))))))))))))))

def pow7_65_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (72 + z * (41 + z * (13 + z * (128 + z * (91 + z * (88 + z * (67 + z * (91 + z * (72 + z * (125 + z * (18 + z * (15 + z * (1 + z * (34 + z * (104 + z * (8 + z * (69 + z * 83))))))))))))))))))

def pow7_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * (49 + z * (87 + z * (131 + z * (103 + z * (61 + z * (7 + z * (86 + z * (68 + z * (56 + z * (99 + z * (153 + z * (86 + z * (169 + z * (233 + z * (176 + z * (179 + z * (176 + z * (287 + z * (325 + z * (224 + z * (274 + z * (134 + z * (89 + z * (302 + z * (261 + z * (135 + z * (221 + z * (192 + z * (217 + z * (188 + z * (204 + z * (133 + z * (65 + z * (53 + z * (102 + z * (38 + z * (1 + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow7_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_64 z * u6 z = pow7_65_q z * f z + pow7_65 z + (131 : R) * pow7_65_mul_t z := by
  simp only [pow7_64, u6, pow7_65_q, f, pow7_65, pow7_65_mul_t]
  simp only [pow6_131]
  ring

theorem pow7_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_64 z * u6 z = pow7_65_q z * f z + pow7_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_65_mul_integer z


theorem pow7_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_64 z * u6 z = pow7_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_65_mul z


theorem pow7_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 65 = pow7_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow7_64_pow z hz]
  exact pow7_65_root z hz


def pow7_130 {R : Type*} [CommRing R] (z : R) : R := (63 + z * (41 + z * (42 + z * (79 + z * (92 + z * (126 + z * (75 + z * (18 + z * (41 + z * (122 + z * (76 + z * (44 + z * (80 + z * (75 + z * (117 + z * (101 + z * (117 + z * (76 + z * (120 + z * 75)))))))))))))))))))

def pow7_130_q {R : Type*} [CommRing R] (z : R) : R := (81 + z * (103 + z * (35 + z * (33 + z * (7 + z * (42 + z * (13 + z * (53 + z * (66 + z * (10 + z * (43 + z * (100 + z * (79 + z * (33 + z * (2 + z * (76 + z * (40 + z * (58 + z * 109))))))))))))))))))

def pow7_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-50) + z * ((-48) + z * (3 + z * (34 + z * ((-29) + z * (70 + z * (59 + z * (134 + z * (279 + z * (294 + z * (333 + z * (323 + z * (408 + z * (558 + z * (644 + z * (528 + z * (558 + z * (598 + z * (513 + z * (670 + z * (644 + z * (594 + z * (384 + z * (435 + z * (500 + z * (344 + z * (304 + z * (205 + z * (149 + z * (100 + z * (120 + z * (144 + z * ((-2) + z * ((-2) + z * ((-61) + z * (50 + z * ((-32) + z * 61))))))))))))))))))))))))))))))))))))))

theorem pow7_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_65 z * pow7_65 z = pow7_130_q z * f z + pow7_130 z + (131 : R) * pow7_130_mul_t z := by
  simp only [pow7_65, pow7_130_q, f, pow7_130, pow7_130_mul_t]
  
  ring

theorem pow7_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_65 z * pow7_65 z = pow7_130_q z * f z + pow7_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_130_mul_integer z


theorem pow7_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_65 z * pow7_65 z = pow7_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_130_mul z


theorem pow7_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 130 = pow7_130 z := by
  calc
    _ = u6 z ^ 65 * u6 z ^ 65 := by ring
    _ = pow7_65 z * pow7_65 z := by rw [pow7_65_pow z hz]
    _ = _ := pow7_130_root z hz


def pow7_131 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (78 + z * (44 + z * (26 + z * (25 + z * (86 + z * (38 + z * (57 + z * (89 + z * (114 + z * (98 + z * (112 + z * (97 + z * (61 + z * (26 + z * (38 + z * (48 + z * (1 + z * (43 + z * 86)))))))))))))))))))

def pow7_131_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (17 + z * (36 + z * (37 + z * (95 + z * (9 + z * (86 + z * (10 + z * (95 + z * (129 + z * (31 + z * (20 + z * (45 + z * (95 + z * (95 + z * (44 + z * (21 + z * (4 + z * 43))))))))))))))))))

def pow7_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * (49 + z * (56 + z * (97 + z * (98 + z * (145 + z * (221 + z * (217 + z * (128 + z * (172 + z * (313 + z * (272 + z * (385 + z * (320 + z * (373 + z * (443 + z * (540 + z * (537 + z * (630 + z * (625 + z * (575 + z * (607 + z * (657 + z * (626 + z * (536 + z * (482 + z * (558 + z * (521 + z * (524 + z * (437 + z * (411 + z * (376 + z * (360 + z * (273 + z * (258 + z * (253 + z * (167 + z * (73 + z * 22))))))))))))))))))))))))))))))))))))))

theorem pow7_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_130 z * u6 z = pow7_131_q z * f z + pow7_131 z + (131 : R) * pow7_131_mul_t z := by
  simp only [pow7_130, u6, pow7_131_q, f, pow7_131, pow7_131_mul_t]
  simp only [pow6_131]
  ring

theorem pow7_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow7_130 z * u6 z = pow7_131_q z * f z + pow7_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow7_131_mul_integer z


theorem pow7_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow7_130 z * u6 z = pow7_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_131_mul z


theorem pow7_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u6 z ^ 131 = pow7_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow7_130_pow z hz]
  exact pow7_131_root z hz


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_131 z

theorem iterate7 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 7) = u7 z := by
  calc
    _ = (z ^ (131 ^ 6)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate6 z hz)
    _ = _ := pow7_131_pow z hz


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (33 + z * (49 + z * (37 + z * (114 + z * (52 + z * (110 + z * (4 + z * (15 + z * (105 + z * (112 + z * (112 + z * (100 + z * (121 + z * (74 + z * (18 + z * (105 + z * (55 + z * (48 + z * 96)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (83 + z * (52 + z * (79 + z * (119 + z * (108 + z * (114 + z * (49 + z * (115 + z * (55 + z * (35 + z * (64 + z * (50 + z * (77 + z * (70 + z * (52 + z * (76 + z * (38 + z * (30 + z * 60))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * (18 + z * ((-5) + z * ((-39) + z * ((-110) + z * ((-133) + z * ((-66) + z * ((-152) + z * ((-151) + z * ((-81) + z * (6 + z * ((-40) + z * ((-70) + z * ((-9) + z * ((-41) + z * ((-118) + z * ((-66) + z * ((-1) + z * ((-40) + z * (34 + z * (74 + z * (81 + z * ((-9) + z * ((-32) + z * (87 + z * (5 + z * ((-23) + z * (87 + z * (85 + z * (20 + z * (41 + z * (8 + z * ((-9) + z * ((-52) + z * ((-25) + z * (8 + z * ((-27) + z * (26 + z * 56))))))))))))))))))))))))))))))))))))))

theorem pow8_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z + (131 : R) * pow8_2_mul_t z := by
  simp only [u7, pow8_2_q, f, pow8_2, pow8_2_mul_t]
  simp only [pow7_131]
  ring

theorem pow8_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_2_mul_integer z


theorem pow8_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z * u7 z = pow8_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_2_mul z


theorem pow8_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 2 = pow8_2 z := by
  calc
    _ = u7 z ^ 1 * u7 z ^ 1 := by ring
    _ = u7 z * u7 z := by simp only [pow_one]
    _ = _ := pow8_2_root z hz


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (41 + z * (0 + z * (46 + z * (1 + z * (66 + z * (31 + z * (23 + z * (83 + z * (73 + z * (95 + z * (125 + z * (126 + z * (23 + z * (75 + z * (40 + z * (105 + z * (42 + z * (51 + z * (29 + z * 35)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (96 + z * (130 + z * (77 + z * (15 + z * (106 + z * (49 + z * (82 + z * (7 + z * (77 + z * (28 + z * (85 + z * (31 + z * (16 + z * (18 + z * (76 + z * (90 + z * (117 + z * (23 + z * 46))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-76) + z * ((-103) + z * ((-80) + z * ((-94) + z * ((-134) + z * ((-111) + z * ((-44) + z * ((-79) + z * ((-167) + z * (2 + z * ((-83) + z * ((-68) + z * ((-33) + z * (155 + z * (215 + z * (151 + z * (88 + z * (138 + z * (119 + z * (254 + z * (223 + z * (441 + z * (381 + z * (301 + z * (379 + z * (226 + z * (199 + z * (326 + z * (319 + z * (305 + z * (161 + z * (168 + z * (59 + z * ((-11) + z * (107 + z * (65 + z * (47 + z * 70))))))))))))))))))))))))))))))))))))))

theorem pow8_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z + (131 : R) * pow8_4_mul_t z := by
  simp only [pow8_2, pow8_4_q, f, pow8_4, pow8_4_mul_t]
  
  ring

theorem pow8_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_4_mul_integer z


theorem pow8_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_2 z * pow8_2 z = pow8_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_4_mul z


theorem pow8_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 4 = pow8_4 z := by
  calc
    _ = u7 z ^ 2 * u7 z ^ 2 := by ring
    _ = pow8_2 z * pow8_2 z := by rw [pow8_2_pow z hz]
    _ = _ := pow8_4_root z hz


def pow8_8 {R : Type*} [CommRing R] (z : R) : R := (102 + z * (32 + z * (110 + z * (76 + z * (0 + z * (88 + z * (55 + z * (40 + z * (113 + z * (87 + z * (57 + z * (4 + z * (37 + z * (35 + z * (53 + z * (58 + z * (93 + z * (71 + z * (28 + z * 53)))))))))))))))))))

def pow8_8_q {R : Type*} [CommRing R] (z : R) : R := (8 + z * (39 + z * (8 + z * (70 + z * (95 + z * (41 + z * (4 + z * (114 + z * (121 + z * (122 + z * (42 + z * (36 + z * (72 + z * (78 + z * (73 + z * (66 + z * (104 + z * (42 + z * 46))))))))))))))))))

def pow8_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * ((-18) + z * (7 + z * ((-50) + z * ((-19) + z * ((-94) + z * ((-53) + z * ((-57) + z * ((-141) + z * ((-141) + z * ((-78) + z * ((-54) + z * ((-191) + z * ((-76) + z * ((-120) + z * ((-27) + z * ((-202) + z * ((-4) + z * (4 + z * (22 + z * ((-89) + z * ((-7) + z * (59 + z * (0 + z * (57 + z * (12 + z * (73 + z * ((-41) + z * (34 + z * ((-17) + z * (39 + z * ((-57) + z * ((-27) + z * ((-46) + z * ((-32) + z * ((-44) + z * ((-9) + z * ((-8) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow8_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z + (131 : R) * pow8_8_mul_t z := by
  simp only [pow8_4, pow8_8_q, f, pow8_8, pow8_8_mul_t]
  
  ring

theorem pow8_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_8_mul_integer z


theorem pow8_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_4 z * pow8_4 z = pow8_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_8_mul z


theorem pow8_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 8 = pow8_8 z := by
  calc
    _ = u7 z ^ 4 * u7 z ^ 4 := by ring
    _ = pow8_4 z * pow8_4 z := by rw [pow8_4_pow z hz]
    _ = _ := pow8_8_root z hz


def pow8_16 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (129 + z * (56 + z * (84 + z * (100 + z * (124 + z * (66 + z * (74 + z * (73 + z * (124 + z * (9 + z * (43 + z * (100 + z * (65 + z * (96 + z * (107 + z * (33 + z * (30 + z * (123 + z * 86)))))))))))))))))))

def pow8_16_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (5 + z * (51 + z * (102 + z * (74 + z * (100 + z * (80 + z * (56 + z * (87 + z * (61 + z * (23 + z * (28 + z * (57 + z * (102 + z * (88 + z * (123 + z * (78 + z * (57 + z * 58))))))))))))))))))

def pow8_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (60 + z * (29 + z * (133 + z * (103 + z * (11 + z * (94 + z * (19 + z * ((-2) + z * (109 + z * (53 + z * (110 + z * (36 + z * ((-14) + z * ((-97) + z * ((-51) + z * ((-50) + z * ((-50) + z * ((-1) + z * ((-22) + z * ((-48) + z * ((-197) + z * ((-124) + z * ((-95) + z * ((-139) + z * ((-46) + z * ((-66) + z * ((-122) + z * ((-95) + z * ((-100) + z * ((-94) + z * ((-88) + z * ((-63) + z * ((-28) + z * ((-15) + z * ((-32) + z * (18 + z * (8 + z * ((-7) + z * 21))))))))))))))))))))))))))))))))))))))

theorem pow8_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z + (131 : R) * pow8_16_mul_t z := by
  simp only [pow8_8, pow8_16_q, f, pow8_16, pow8_16_mul_t]
  
  ring

theorem pow8_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_16_mul_integer z


theorem pow8_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_8 z * pow8_8 z = pow8_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_16_mul z


theorem pow8_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 16 = pow8_16 z := by
  calc
    _ = u7 z ^ 8 * u7 z ^ 8 := by ring
    _ = pow8_8 z * pow8_8 z := by rw [pow8_8_pow z hz]
    _ = _ := pow8_16_root z hz


def pow8_32 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (37 + z * (47 + z * (101 + z * (26 + z * (13 + z * (120 + z * (11 + z * (4 + z * (85 + z * (49 + z * (101 + z * (62 + z * (65 + z * (49 + z * (100 + z * (5 + z * (125 + z * (113 + z * 110)))))))))))))))))))

def pow8_32_q {R : Type*} [CommRing R] (z : R) : R := (62 + z * (113 + z * (106 + z * (86 + z * (40 + z * (99 + z * (71 + z * (82 + z * (11 + z * (102 + z * (53 + z * (33 + z * (26 + z * (52 + z * (113 + z * (111 + z * (29 + z * (35 + z * 60))))))))))))))))))

def pow8_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * (21 + z * (53 + z * (29 + z * (105 + z * (124 + z * (173 + z * (128 + z * (195 + z * (210 + z * (242 + z * (92 + z * (186 + z * (225 + z * (140 + z * (268 + z * (315 + z * (226 + z * (232 + z * (379 + z * (371 + z * (335 + z * (240 + z * (371 + z * (356 + z * (103 + z * (148 + z * (316 + z * (178 + z * (111 + z * (195 + z * (154 + z * (172 + z * (184 + z * (87 + z * (46 + z * (110 + z * (131 + z * 56))))))))))))))))))))))))))))))))))))))

theorem pow8_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_16 z * pow8_16 z = pow8_32_q z * f z + pow8_32 z + (131 : R) * pow8_32_mul_t z := by
  simp only [pow8_16, pow8_32_q, f, pow8_32, pow8_32_mul_t]
  
  ring

theorem pow8_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_16 z * pow8_16 z = pow8_32_q z * f z + pow8_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_32_mul_integer z


theorem pow8_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_16 z * pow8_16 z = pow8_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_32_mul z


theorem pow8_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 32 = pow8_32 z := by
  calc
    _ = u7 z ^ 16 * u7 z ^ 16 := by ring
    _ = pow8_16 z * pow8_16 z := by rw [pow8_16_pow z hz]
    _ = _ := pow8_32_root z hz


def pow8_64 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (9 + z * (64 + z * (50 + z * (45 + z * (95 + z * (117 + z * (2 + z * (47 + z * (30 + z * (77 + z * (95 + z * (47 + z * (9 + z * (127 + z * (86 + z * (126 + z * (121 + z * (96 + z * 9)))))))))))))))))))

def pow8_64_q {R : Type*} [CommRing R] (z : R) : R := (43 + z * (34 + z * (59 + z * (89 + z * (93 + z * (35 + z * (130 + z * (122 + z * (5 + z * (60 + z * (17 + z * (5 + z * (116 + z * (113 + z * (94 + z * (55 + z * (129 + z * (77 + z * 48))))))))))))))))))

def pow8_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-20) + z * ((-35) + z * ((-30) + z * ((-46) + z * ((-67) + z * ((-55) + z * ((-130) + z * ((-177) + z * ((-64) + z * ((-139) + z * ((-257) + z * ((-17) + z * ((-122) + z * ((-234) + z * ((-93) + z * ((-149) + z * ((-192) + z * ((-150) + z * ((-142) + z * (19 + z * (79 + z * ((-52) + z * ((-10) + z * (49 + z * ((-90) + z * (57 + z * (84 + z * (199 + z * (128 + z * (223 + z * (68 + z * (155 + z * (79 + z * (149 + z * (106 + z * (246 + z * (165 + z * 92))))))))))))))))))))))))))))))))))))))

theorem pow8_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_32 z * pow8_32 z = pow8_64_q z * f z + pow8_64 z + (131 : R) * pow8_64_mul_t z := by
  simp only [pow8_32, pow8_64_q, f, pow8_64, pow8_64_mul_t]
  
  ring

theorem pow8_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_32 z * pow8_32 z = pow8_64_q z * f z + pow8_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_64_mul_integer z


theorem pow8_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_32 z * pow8_32 z = pow8_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_64_mul z


theorem pow8_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 64 = pow8_64 z := by
  calc
    _ = u7 z ^ 32 * u7 z ^ 32 := by ring
    _ = pow8_32 z * pow8_32 z := by rw [pow8_32_pow z hz]
    _ = _ := pow8_64_root z hz


def pow8_65 {R : Type*} [CommRing R] (z : R) : R := (78 + z * (11 + z * (55 + z * (1 + z * (99 + z * (92 + z * (65 + z * (59 + z * (52 + z * (62 + z * (115 + z * (61 + z * (77 + z * (117 + z * (58 + z * (79 + z * (109 + z * (52 + z * (76 + z * 35)))))))))))))))))))

def pow8_65_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (124 + z * (34 + z * (75 + z * (55 + z * (99 + z * (128 + z * (28 + z * (42 + z * (60 + z * (38 + z * (14 + z * (83 + z * (30 + z * (113 + z * (85 + z * (119 + z * (3 + z * 119))))))))))))))))))

def pow8_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-43) + z * ((-43) + z * ((-42) + z * ((-42) + z * ((-99) + z * ((-90) + z * ((-39) + z * ((-147) + z * ((-121) + z * ((-76) + z * (3 + z * ((-44) + z * ((-62) + z * ((-54) + z * (120 + z * (12 + z * ((-49) + z * (1 + z * ((-11) + z * ((-52) + z * (45 + z * (66 + z * (17 + z * (173 + z * (129 + z * (159 + z * (129 + z * (140 + z * (86 + z * (70 + z * ((-79) + z * ((-31) + z * (11 + z * ((-40) + z * (20 + z * (55 + z * (6 + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow8_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_64 z * u7 z = pow8_65_q z * f z + pow8_65 z + (131 : R) * pow8_65_mul_t z := by
  simp only [pow8_64, u7, pow8_65_q, f, pow8_65, pow8_65_mul_t]
  simp only [pow7_131]
  ring

theorem pow8_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_64 z * u7 z = pow8_65_q z * f z + pow8_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_65_mul_integer z


theorem pow8_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_64 z * u7 z = pow8_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_65_mul z


theorem pow8_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 65 = pow8_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow8_64_pow z hz]
  exact pow8_65_root z hz


def pow8_130 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (101 + z * (30 + z * (51 + z * (34 + z * (94 + z * (59 + z * (129 + z * (80 + z * (21 + z * (107 + z * (42 + z * (30 + z * (117 + z * (115 + z * (58 + z * (77 + z * (100 + z * 75))))))))))))))))))

def pow8_130_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (19 + z * (5 + z * (9 + z * (95 + z * (118 + z * (26 + z * (45 + z * (130 + z * (75 + z * (122 + z * (126 + z * (74 + z * (31 + z * (124 + z * (63 + z * (58 + z * (57 + z * 46))))))))))))))))))

def pow8_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (45 + z * (4 + z * (56 + z * ((-5) + z * (94 + z * (29 + z * (56 + z * (47 + z * (31 + z * (5 + z * (74 + z * (60 + z * ((-22) + z * ((-9) + z * (115 + z * (68 + z * ((-17) + z * (114 + z * (169 + z * (40 + z * (178 + z * (76 + z * (99 + z * (129 + z * (120 + z * (131 + z * (129 + z * (47 + z * (174 + z * (141 + z * (84 + z * (168 + z * (131 + z * (46 + z * (79 + z * (46 + z * (22 + z * (17 + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow8_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_65 z * pow8_65 z = pow8_130_q z * f z + pow8_130 z + (131 : R) * pow8_130_mul_t z := by
  simp only [pow8_65, pow8_130_q, f, pow8_130, pow8_130_mul_t]
  
  ring

theorem pow8_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_65 z * pow8_65 z = pow8_130_q z * f z + pow8_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_130_mul_integer z


theorem pow8_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_65 z * pow8_65 z = pow8_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_130_mul z


theorem pow8_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 130 = pow8_130 z := by
  calc
    _ = u7 z ^ 65 * u7 z ^ 65 := by ring
    _ = pow8_65 z * pow8_65 z := by rw [pow8_65_pow z hz]
    _ = _ := pow8_130_root z hz


def pow8_131 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (43 + z * (109 + z * (0 + z * (108 + z * (101 + z * (85 + z * (95 + z * (92 + z * (72 + z * (7 + z * (15 + z * (129 + z * (44 + z * (70 + z * (59 + z * (9 + z * (99 + z * (55 + z * 77)))))))))))))))))))

def pow8_131_q {R : Type*} [CommRing R] (z : R) : R := (49 + z * (95 + z * (9 + z * (127 + z * (49 + z * (0 + z * (14 + z * (75 + z * (56 + z * (75 + z * (102 + z * (43 + z * (87 + z * (111 + z * (18 + z * (21 + z * (85 + z * 31)))))))))))))))))

def pow8_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * (13 + z * (24 + z * ((-25) + z * ((-30) + z * ((-47) + z * (46 + z * (58 + z * ((-12) + z * (52 + z * (119 + z * (45 + z * (26 + z * (128 + z * (67 + z * (139 + z * (157 + z * (136 + z * (169 + z * (197 + z * (78 + z * (59 + z * (197 + z * (225 + z * (164 + z * (196 + z * (259 + z * (147 + z * (58 + z * (93 + z * (71 + z * (17 + z * (50 + z * (82 + z * (31 + z * (27 + z * (74 + z * 49)))))))))))))))))))))))))))))))))))))

theorem pow8_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_130 z * u7 z = pow8_131_q z * f z + pow8_131 z + (131 : R) * pow8_131_mul_t z := by
  simp only [pow8_130, u7, pow8_131_q, f, pow8_131, pow8_131_mul_t]
  simp only [pow7_131]
  ring

theorem pow8_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow8_130 z * u7 z = pow8_131_q z * f z + pow8_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow8_131_mul_integer z


theorem pow8_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow8_130 z * u7 z = pow8_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_131_mul z


theorem pow8_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u7 z ^ 131 = pow8_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow8_130_pow z hz]
  exact pow8_131_root z hz


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_131 z

theorem iterate8 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 8) = u8 z := by
  calc
    _ = (z ^ (131 ^ 7)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u7 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate7 z hz)
    _ = _ := pow8_131_pow z hz

end DimensionTen.Mod131

end

end OAI
