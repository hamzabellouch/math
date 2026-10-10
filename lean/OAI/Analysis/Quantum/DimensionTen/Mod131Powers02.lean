import OAI.Analysis.Quantum.DimensionTen.Mod131Powers01

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow3_2 {R : Type*} [CommRing R] (z : R) : R := (75 + z * (39 + z * (20 + z * (18 + z * (122 + z * (2 + z * (109 + z * (115 + z * (82 + z * (19 + z * (87 + z * (123 + z * (29 + z * (90 + z * (0 + z * (85 + z * (93 + z * (124 + z * (88 + z * 67)))))))))))))))))))

def pow3_2_q {R : Type*} [CommRing R] (z : R) : R := (121 + z * (17 + z * (55 + z * (80 + z * (85 + z * (48 + z * (79 + z * (2 + z * (8 + z * (99 + z * (72 + z * (38 + z * (62 + z * (87 + z * (25 + z * (19 + z * (60 + z * (6 + z * 4))))))))))))))))))

def pow3_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-44) + z * ((-18) + z * (28 + z * (70 + z * (78 + z * ((-1) + z * (66 + z * (77 + z * (75 + z * (186 + z * (246 + z * (22 + z * (149 + z * (65 + z * (30 + z * (213 + z * (120 + z * (113 + z * (242 + z * (371 + z * (480 + z * (348 + z * (319 + z * (323 + z * (306 + z * (390 + z * (431 + z * (318 + z * (253 + z * (141 + z * (223 + z * (224 + z * (209 + z * (300 + z * (225 + z * (251 + z * (299 + z * (252 + z * 127))))))))))))))))))))))))))))))))))))))

theorem pow3_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z + (131 : R) * pow3_2_mul_t z := by
  simp only [u2, pow3_2_q, f, pow3_2, pow3_2_mul_t]
  simp only [pow2_131]
  ring

theorem pow3_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_2_mul_integer z


theorem pow3_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z * u2 z = pow3_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_2_mul z


theorem pow3_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 2 = pow3_2 z := by
  calc
    _ = u2 z ^ 1 * u2 z ^ 1 := by ring
    _ = u2 z * u2 z := by simp only [pow_one]
    _ = _ := pow3_2_root z hz


def pow3_4 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (52 + z * (70 + z * (36 + z * (14 + z * (21 + z * (64 + z * (101 + z * (75 + z * (130 + z * (49 + z * (113 + z * (97 + z * (63 + z * (96 + z * (56 + z * (117 + z * (120 + z * (94 + z * 90)))))))))))))))))))

def pow3_4_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (44 + z * (30 + z * (7 + z * (52 + z * (90 + z * (50 + z * (46 + z * (82 + z * (54 + z * (127 + z * (18 + z * (27 + z * (102 + z * (4 + z * (15 + z * (0 + z * (50 + z * 35))))))))))))))))))

def pow3_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-12) + z * ((-47) + z * ((-22) + z * (49 + z * ((-101) + z * (31 + z * (52 + z * (79 + z * ((-132) + z * (89 + z * (126 + z * (6 + z * ((-8) + z * (160 + z * (144 + z * (90 + z * (305 + z * (123 + z * (350 + z * (197 + z * (268 + z * (310 + z * (468 + z * (369 + z * (307 + z * (315 + z * (315 + z * (331 + z * (222 + z * (271 + z * (177 + z * (244 + z * (238 + z * (280 + z * (226 + z * (145 + z * (72 + z * 34))))))))))))))))))))))))))))))))))))))

theorem pow3_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z + (131 : R) * pow3_4_mul_t z := by
  simp only [pow3_2, pow3_4_q, f, pow3_4, pow3_4_mul_t]
  
  ring

theorem pow3_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_4_mul_integer z


theorem pow3_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_2 z * pow3_2 z = pow3_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_4_mul z


theorem pow3_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 4 = pow3_4 z := by
  calc
    _ = u2 z ^ 2 * u2 z ^ 2 := by ring
    _ = pow3_2 z * pow3_2 z := by rw [pow3_2_pow z hz]
    _ = _ := pow3_4_root z hz


def pow3_8 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (129 + z * (2 + z * (4 + z * (35 + z * (125 + z * (121 + z * (23 + z * (32 + z * (70 + z * (78 + z * (85 + z * (127 + z * (32 + z * (96 + z * (58 + z * (64 + z * (24 + z * (71 + z * 4)))))))))))))))))))

def pow3_8_q {R : Type*} [CommRing R] (z : R) : R := (79 + z * (5 + z * (86 + z * (105 + z * (8 + z * (110 + z * (2 + z * (130 + z * (67 + z * (61 + z * (77 + z * (54 + z * (24 + z * (101 + z * (89 + z * (96 + z * (16 + z * (32 + z * 109))))))))))))))))))

def pow3_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (89 + z * (68 + z * (81 + z * (37 + z * ((-34) + z * ((-94) + z * (48 + z * ((-6) + z * (52 + z * (193 + z * (11 + z * (122 + z * (76 + z * (87 + z * (141 + z * (68 + z * (230 + z * (384 + z * (284 + z * (341 + z * (277 + z * (249 + z * (189 + z * (325 + z * (414 + z * (493 + z * (355 + z * (440 + z * (509 + z * (306 + z * (353 + z * (275 + z * (279 + z * (280 + z * (215 + z * (269 + z * (167 + z * (74 + z * 61))))))))))))))))))))))))))))))))))))))

theorem pow3_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z + (131 : R) * pow3_8_mul_t z := by
  simp only [pow3_4, pow3_8_q, f, pow3_8, pow3_8_mul_t]
  
  ring

theorem pow3_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_8_mul_integer z


theorem pow3_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_4 z * pow3_4 z = pow3_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_8_mul z


theorem pow3_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 8 = pow3_8 z := by
  calc
    _ = u2 z ^ 4 * u2 z ^ 4 := by ring
    _ = pow3_4 z * pow3_4 z := by rw [pow3_4_pow z hz]
    _ = _ := pow3_8_root z hz


def pow3_16 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (50 + z * (108 + z * (129 + z * (49 + z * (2 + z * (71 + z * (28 + z * (33 + z * (54 + z * (24 + z * (4 + z * (65 + z * (128 + z * (120 + z * (22 + z * (51 + z * (64 + z * (35 + z * 67)))))))))))))))))))

def pow3_16_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (65 + z * (130 + z * (37 + z * (117 + z * (60 + z * (66 + z * (108 + z * (29 + z * (84 + z * (78 + z * (27 + z * (73 + z * (11 + z * (105 + z * (121 + z * (79 + z * (36 + z * 16))))))))))))))))))

def pow3_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-23) + z * ((-17) + z * (22 + z * ((-100) + z * ((-152) + z * ((-98) + z * (38 + z * ((-34) + z * ((-201) + z * ((-233) + z * (6 + z * (10 + z * ((-77) + z * ((-54) + z * ((-174) + z * (2 + z * (11 + z * (24 + z * ((-66) + z * ((-15) + z * ((-62) + z * (11 + z * (16 + z * (22 + z * (155 + z * ((-31) + z * (26 + z * (6 + z * (42 + z * (53 + z * (84 + z * ((-60) + z * ((-3) + z * ((-73) + z * ((-44) + z * ((-33) + z * (14 + z * ((-4) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow3_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z + (131 : R) * pow3_16_mul_t z := by
  simp only [pow3_8, pow3_16_q, f, pow3_16, pow3_16_mul_t]
  
  ring

theorem pow3_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_16_mul_integer z


theorem pow3_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_8 z * pow3_8 z = pow3_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_16_mul z


theorem pow3_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 16 = pow3_16 z := by
  calc
    _ = u2 z ^ 8 * u2 z ^ 8 := by ring
    _ = pow3_8 z * pow3_8 z := by rw [pow3_8_pow z hz]
    _ = _ := pow3_16_root z hz


def pow3_32 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (71 + z * (12 + z * (111 + z * (75 + z * (102 + z * (33 + z * (31 + z * (18 + z * (56 + z * (12 + z * (22 + z * (54 + z * (125 + z * (57 + z * (130 + z * (65 + z * (55 + z * (62 + z * 94)))))))))))))))))))

def pow3_32_q {R : Type*} [CommRing R] (z : R) : R := (72 + z * (113 + z * (109 + z * (84 + z * (60 + z * (27 + z * (9 + z * (90 + z * (126 + z * (128 + z * (87 + z * (42 + z * (18 + z * (101 + z * (56 + z * (50 + z * (127 + z * (22 + z * 35))))))))))))))))))

def pow3_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-55) + z * ((-67) + z * ((-20) + z * (36 + z * (34 + z * (14 + z * ((-80) + z * ((-142) + z * ((-154) + z * ((-159) + z * ((-212) + z * ((-258) + z * ((-323) + z * ((-215) + z * ((-21) + z * (28 + z * ((-95) + z * ((-257) + z * ((-134) + z * ((-165) + z * ((-201) + z * ((-26) + z * ((-112) + z * ((-243) + z * ((-119) + z * ((-49) + z * ((-42) + z * ((-24) + z * ((-45) + z * (100 + z * (103 + z * (50 + z * (61 + z * ((-33) + z * ((-1) + z * (47 + z * (18 + z * 34))))))))))))))))))))))))))))))))))))))

theorem pow3_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_16 z * pow3_16 z = pow3_32_q z * f z + pow3_32 z + (131 : R) * pow3_32_mul_t z := by
  simp only [pow3_16, pow3_32_q, f, pow3_32, pow3_32_mul_t]
  
  ring

theorem pow3_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_16 z * pow3_16 z = pow3_32_q z * f z + pow3_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_32_mul_integer z


theorem pow3_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_16 z * pow3_16 z = pow3_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_32_mul z


theorem pow3_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 32 = pow3_32 z := by
  calc
    _ = u2 z ^ 16 * u2 z ^ 16 := by ring
    _ = pow3_16 z * pow3_16 z := by rw [pow3_16_pow z hz]
    _ = _ := pow3_32_root z hz


def pow3_64 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (70 + z * (87 + z * (100 + z * (13 + z * (65 + z * (19 + z * (78 + z * (25 + z * (23 + z * (80 + z * (126 + z * (44 + z * (99 + z * (84 + z * (99 + z * (25 + z * (116 + z * (119 + z * 129)))))))))))))))))))

def pow3_64_q {R : Type*} [CommRing R] (z : R) : R := (68 + z * (126 + z * (110 + z * (6 + z * (7 + z * (34 + z * (56 + z * (31 + z * (2 + z * (32 + z * (107 + z * (113 + z * (121 + z * (110 + z * (120 + z * (49 + z * (10 + z * (33 + z * 59))))))))))))))))))

def pow3_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-34) + z * ((-76) + z * ((-42) + z * (45 + z * ((-8) + z * (28 + z * (11 + z * (90 + z * ((-17) + z * ((-27) + z * ((-142) + z * ((-142) + z * ((-199) + z * ((-148) + z * ((-117) + z * (102 + z * ((-50) + z * (48 + z * (15 + z * (129 + z * ((-5) + z * (53 + z * ((-76) + z * (33 + z * ((-123) + z * ((-53) + z * (17 + z * (141 + z * ((-18) + z * (69 + z * (145 + z * (227 + z * (134 + z * (190 + z * (103 + z * (65 + z * (59 + z * 67))))))))))))))))))))))))))))))))))))))

theorem pow3_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_32 z * pow3_32 z = pow3_64_q z * f z + pow3_64 z + (131 : R) * pow3_64_mul_t z := by
  simp only [pow3_32, pow3_64_q, f, pow3_64, pow3_64_mul_t]
  
  ring

theorem pow3_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_32 z * pow3_32 z = pow3_64_q z * f z + pow3_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_64_mul_integer z


theorem pow3_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_32 z * pow3_32 z = pow3_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_64_mul z


theorem pow3_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 64 = pow3_64 z := by
  calc
    _ = u2 z ^ 32 * u2 z ^ 32 := by ring
    _ = pow3_32 z * pow3_32 z := by rw [pow3_32_pow z hz]
    _ = _ := pow3_64_root z hz


def pow3_65 {R : Type*} [CommRing R] (z : R) : R := (60 + z * (32 + z * (98 + z * (58 + z * (82 + z * (34 + z * (4 + z * (116 + z * (28 + z * (129 + z * (127 + z * (111 + z * (52 + z * (39 + z * (71 + z * (17 + z * (86 + z * (44 + z * (83 + z * 18)))))))))))))))))))

def pow3_65_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (78 + z * (9 + z * (105 + z * (125 + z * (7 + z * (42 + z * (37 + z * (91 + z * (110 + z * (88 + z * (62 + z * (43 + z * (106 + z * (41 + z * (64 + z * (18 + z * (26 + z * 4))))))))))))))))))

def pow3_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * (84 + z * (105 + z * (145 + z * (135 + z * (54 + z * (114 + z * (146 + z * (70 + z * (106 + z * (99 + z * (53 + z * (59 + z * (34 + z * (126 + z * (21 + z * (128 + z * (167 + z * (314 + z * (413 + z * (333 + z * (318 + z * (229 + z * (205 + z * (248 + z * (273 + z * (240 + z * (240 + z * (254 + z * (303 + z * (290 + z * (277 + z * (291 + z * (304 + z * (247 + z * (252 + z * (305 + z * (242 + z * 127))))))))))))))))))))))))))))))))))))))

theorem pow3_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_64 z * u2 z = pow3_65_q z * f z + pow3_65 z + (131 : R) * pow3_65_mul_t z := by
  simp only [pow3_64, u2, pow3_65_q, f, pow3_65, pow3_65_mul_t]
  simp only [pow2_131]
  ring

theorem pow3_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_64 z * u2 z = pow3_65_q z * f z + pow3_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_65_mul_integer z


theorem pow3_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_64 z * u2 z = pow3_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_65_mul z


theorem pow3_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 65 = pow3_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow3_64_pow z hz]
  exact pow3_65_root z hz


def pow3_130 {R : Type*} [CommRing R] (z : R) : R := (43 + z * (11 + z * (68 + z * (21 + z * (104 + z * (15 + z * (46 + z * (106 + z * (40 + z * (16 + z * (6 + z * (76 + z * (92 + z * (16 + z * (39 + z * (23 + z * (41 + z * (3 + z * (106 + z * 48)))))))))))))))))))

def pow3_130_q {R : Type*} [CommRing R] (z : R) : R := (79 + z * (39 + z * (72 + z * (126 + z * (26 + z * (106 + z * (40 + z * (64 + z * (69 + z * (80 + z * (100 + z * (61 + z * (36 + z * (3 + z * (99 + z * (57 + z * (127 + z * (75 + z * 62))))))))))))))))))

def pow3_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-14) + z * (17 + z * ((-6) + z * (36 + z * ((-56) + z * (6 + z * ((-38) + z * ((-124) + z * (75 + z * ((-37) + z * (132 + z * (85 + z * (92 + z * (101 + z * ((-57) + z * (22 + z * (27 + z * (121 + z * (27 + z * (193 + z * (52 + z * ((-62) + z * (51 + z * ((-18) + z * (100 + z * (28 + z * (56 + z * (59 + z * ((-23) + z * ((-3) + z * ((-37) + z * ((-7) + z * ((-91) + z * ((-27) + z * ((-42) + z * ((-2) + z * ((-9) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow3_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_65 z * pow3_65 z = pow3_130_q z * f z + pow3_130 z + (131 : R) * pow3_130_mul_t z := by
  simp only [pow3_65, pow3_130_q, f, pow3_130, pow3_130_mul_t]
  
  ring

theorem pow3_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_65 z * pow3_65 z = pow3_130_q z * f z + pow3_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_130_mul_integer z


theorem pow3_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_65 z * pow3_65 z = pow3_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_130_mul z


theorem pow3_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 130 = pow3_130 z := by
  calc
    _ = u2 z ^ 65 * u2 z ^ 65 := by ring
    _ = pow3_65 z * pow3_65 z := by rw [pow3_65_pow z hz]
    _ = _ := pow3_130_root z hz


def pow3_131 {R : Type*} [CommRing R] (z : R) : R := (109 + z * (34 + z * (52 + z * (118 + z * (34 + z * (65 + z * (52 + z * (30 + z * (23 + z * (129 + z * (57 + z * (124 + z * (76 + z * (44 + z * (15 + z * (50 + z * (60 + z * (93 + z * (44 + z * 52)))))))))))))))))))

def pow3_131_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (54 + z * (114 + z * (109 + z * (104 + z * (128 + z * (50 + z * (76 + z * (99 + z * (58 + z * (89 + z * (101 + z * (62 + z * (110 + z * (9 + z * (71 + z * (71 + z * (2 + z * 35))))))))))))))))))

def pow3_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-32) + z * ((-18) + z * ((-69) + z * ((-25) + z * ((-102) + z * ((-104) + z * ((-93) + z * ((-131) + z * ((-109) + z * ((-146) + z * ((-143) + z * ((-205) + z * ((-259) + z * ((-239) + z * ((-165) + z * ((-263) + z * ((-297) + z * ((-271) + z * ((-230) + z * ((-110) + z * ((-171) + z * ((-76) + z * ((-73) + z * ((-116) + z * ((-121) + z * (86 + z * (21 + z * ((-45) + z * ((-36) + z * ((-30) + z * (123 + z * (30 + z * (34 + z * (88 + z * (36 + z * (86 + z * (123 + z * (134 + z * 47))))))))))))))))))))))))))))))))))))))

theorem pow3_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_130 z * u2 z = pow3_131_q z * f z + pow3_131 z + (131 : R) * pow3_131_mul_t z := by
  simp only [pow3_130, u2, pow3_131_q, f, pow3_131, pow3_131_mul_t]
  simp only [pow2_131]
  ring

theorem pow3_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow3_130 z * u2 z = pow3_131_q z * f z + pow3_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow3_131_mul_integer z


theorem pow3_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow3_130 z * u2 z = pow3_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_131_mul z


theorem pow3_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u2 z ^ 131 = pow3_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow3_130_pow z hz]
  exact pow3_131_root z hz


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_131 z

theorem iterate3 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 3) = u3 z := by
  calc
    _ = (z ^ (131 ^ 2)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u2 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate2 z hz)
    _ = _ := pow3_131_pow z hz


def pow4_2 {R : Type*} [CommRing R] (z : R) : R := (77 + z * (94 + z * (126 + z * (63 + z * (100 + z * (23 + z * (63 + z * (7 + z * (112 + z * (76 + z * (8 + z * (23 + z * (14 + z * (127 + z * (25 + z * (16 + z * (32 + z * (56 + z * (129 + z * 73)))))))))))))))))))

def pow4_2_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (37 + z * (27 + z * (27 + z * (62 + z * (100 + z * (126 + z * (4 + z * (79 + z * (21 + z * (52 + z * (10 + z * (6 + z * (42 + z * (42 + z * (55 + z * (62 + z * (80 + z * 84))))))))))))))))))

def pow4_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (84 + z * (36 + z * (63 + z * (182 + z * (76 + z * (107 + z * (87 + z * (36 + z * (20 + z * (159 + z * (18 + z * (203 + z * (289 + z * (84 + z * (219 + z * (183 + z * (147 + z * (76 + z * (156 + z * (153 + z * (274 + z * (120 + z * (137 + z * (37 + z * (53 + z * (4 + z * (112 + z * (128 + z * (211 + z * (50 + z * (73 + z * (12 + z * (15 + z * ((-15) + z * (5 + z * (11 + z * (10 + z * ((-8) + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow4_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z + (131 : R) * pow4_2_mul_t z := by
  simp only [u3, pow4_2_q, f, pow4_2, pow4_2_mul_t]
  simp only [pow3_131]
  ring

theorem pow4_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_2_mul_integer z


theorem pow4_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z * u3 z = pow4_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_2_mul z


theorem pow4_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 2 = pow4_2 z := by
  calc
    _ = u3 z ^ 1 * u3 z ^ 1 := by ring
    _ = u3 z * u3 z := by simp only [pow_one]
    _ = _ := pow4_2_root z hz


def pow4_4 {R : Type*} [CommRing R] (z : R) : R := (71 + z * (75 + z * (88 + z * (2 + z * (94 + z * (58 + z * (61 + z * (1 + z * (83 + z * (27 + z * (62 + z * (83 + z * (130 + z * (51 + z * (121 + z * (112 + z * (103 + z * (6 + z * (117 + z * 46)))))))))))))))))))

def pow4_4_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (10 + z * (92 + z * (28 + z * (57 + z * (83 + z * (126 + z * (38 + z * (59 + z * (4 + z * (28 + z * (125 + z * (115 + z * (23 + z * (20 + z * (101 + z * (117 + z * (122 + z * 89))))))))))))))))))

def pow4_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (81 + z * (142 + z * (194 + z * (212 + z * (143 + z * (159 + z * ((-4) + z * (133 + z * (115 + z * (153 + z * ((-30) + z * (5 + z * ((-74) + z * (41 + z * ((-1) + z * ((-155) + z * ((-44) + z * ((-89) + z * ((-3) + z * ((-11) + z * (104 + z * ((-34) + z * ((-294) + z * ((-245) + z * ((-168) + z * (74 + z * ((-47) + z * ((-237) + z * ((-232) + z * ((-125) + z * (60 + z * (37 + z * ((-118) + z * ((-103) + z * ((-2) + z * (87 + z * (98 + z * 40))))))))))))))))))))))))))))))))))))))

theorem pow4_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z + (131 : R) * pow4_4_mul_t z := by
  simp only [pow4_2, pow4_4_q, f, pow4_4, pow4_4_mul_t]
  
  ring

theorem pow4_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_4_mul_integer z


theorem pow4_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_2 z * pow4_2 z = pow4_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_4_mul z


theorem pow4_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 4 = pow4_4 z := by
  calc
    _ = u3 z ^ 2 * u3 z ^ 2 := by ring
    _ = pow4_2 z * pow4_2 z := by rw [pow4_2_pow z hz]
    _ = _ := pow4_4_root z hz


def pow4_8 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (20 + z * (92 + z * (36 + z * (99 + z * (72 + z * (51 + z * (73 + z * (123 + z * (49 + z * (18 + z * (23 + z * (115 + z * (64 + z * (12 + z * (103 + z * (88 + z * (25 + z * (125 + z * 104)))))))))))))))))))

def pow4_8_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (56 + z * (102 + z * (61 + z * (18 + z * (68 + z * (28 + z * (18 + z * (86 + z * (10 + z * (110 + z * (5 + z * (98 + z * (87 + z * (19 + z * (110 + z * (86 + z * (12 + z * 20))))))))))))))))))

def pow4_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * (16 + z * (19 + z * ((-6) + z * (8 + z * ((-44) + z * (98 + z * ((-90) + z * ((-11) + z * ((-39) + z * (8 + z * ((-55) + z * (93 + z * ((-21) + z * (179 + z * (92 + z * (327 + z * (56 + z * (202 + z * (156 + z * (301 + z * ((-30) + z * (303 + z * (173 + z * (252 + z * (162 + z * (328 + z * (266 + z * (260 + z * (252 + z * (433 + z * (165 + z * (188 + z * (189 + z * (151 + z * (26 + z * (93 + z * (72 + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow4_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z + (131 : R) * pow4_8_mul_t z := by
  simp only [pow4_4, pow4_8_q, f, pow4_8, pow4_8_mul_t]
  
  ring

theorem pow4_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_8_mul_integer z


theorem pow4_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_4 z * pow4_4 z = pow4_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_8_mul z


theorem pow4_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 8 = pow4_8 z := by
  calc
    _ = u3 z ^ 4 * u3 z ^ 4 := by ring
    _ = pow4_4 z * pow4_4 z := by rw [pow4_4_pow z hz]
    _ = _ := pow4_8_root z hz


def pow4_16 {R : Type*} [CommRing R] (z : R) : R := (122 + z * (26 + z * (31 + z * (76 + z * (68 + z * (95 + z * (29 + z * (108 + z * (99 + z * (121 + z * (66 + z * (103 + z * (89 + z * (31 + z * (97 + z * (117 + z * (52 + z * (87 + z * (2 + z * 60)))))))))))))))))))

def pow4_16_q {R : Type*} [CommRing R] (z : R) : R := (55 + z * (125 + z * (41 + z * (42 + z * (109 + z * (25 + z * (125 + z * (126 + z * (87 + z * (42 + z * (125 + z * (30 + z * (2 + z * (70 + z * (50 + z * (62 + z * (6 + z * (25 + z * 74))))))))))))))))))

def pow4_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (88 + z * ((-31) + z * (84 + z * ((-8) + z * (128 + z * (20 + z * (15 + z * (90 + z * (84 + z * ((-14) + z * (46 + z * ((-92) + z * (51 + z * (10 + z * ((-51) + z * (5 + z * (189 + z * (27 + z * (70 + z * (125 + z * (267 + z * (209 + z * (66 + z * (210 + z * (284 + z * (101 + z * (76 + z * (276 + z * (192 + z * ((-5) + z * (221 + z * (309 + z * (127 + z * (156 + z * (244 + z * (145 + z * (113 + z * (161 + z * 82))))))))))))))))))))))))))))))))))))))

theorem pow4_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z + (131 : R) * pow4_16_mul_t z := by
  simp only [pow4_8, pow4_16_q, f, pow4_16, pow4_16_mul_t]
  
  ring

theorem pow4_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_16_mul_integer z


theorem pow4_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_8 z * pow4_8 z = pow4_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_16_mul z


theorem pow4_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 16 = pow4_16 z := by
  calc
    _ = u3 z ^ 8 * u3 z ^ 8 := by ring
    _ = pow4_8 z * pow4_8 z := by rw [pow4_8_pow z hz]
    _ = _ := pow4_16_root z hz


def pow4_32 {R : Type*} [CommRing R] (z : R) : R := (46 + z * (1 + z * (119 + z * (45 + z * (77 + z * (113 + z * (50 + z * (95 + z * (45 + z * (20 + z * (98 + z * (19 + z * (128 + z * (83 + z * (21 + z * (104 + z * (35 + z * (120 + z * (94 + z * 65)))))))))))))))))))

def pow4_32_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (29 + z * (63 + z * (15 + z * (96 + z * (28 + z * (63 + z * (60 + z * (94 + z * (67 + z * (117 + z * (69 + z * (92 + z * (86 + z * (78 + z * (22 + z * (40 + z * (12 + z * 63))))))))))))))))))

def pow4_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (98 + z * (23 + z * (8 + z * (104 + z * (64 + z * (125 + z * (24 + z * (175 + z * (181 + z * (177 + z * (183 + z * (211 + z * (256 + z * (101 + z * (313 + z * (288 + z * (308 + z * (334 + z * (238 + z * (384 + z * (288 + z * (200 + z * (323 + z * (231 + z * (347 + z * (154 + z * (260 + z * (148 + z * (188 + z * (88 + z * (103 + z * (126 + z * (87 + z * (71 + z * (91 + z * (1 + z * (45 + z * ((-30) + z * 27))))))))))))))))))))))))))))))))))))))

theorem pow4_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_16 z * pow4_16 z = pow4_32_q z * f z + pow4_32 z + (131 : R) * pow4_32_mul_t z := by
  simp only [pow4_16, pow4_32_q, f, pow4_32, pow4_32_mul_t]
  
  ring

theorem pow4_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_16 z * pow4_16 z = pow4_32_q z * f z + pow4_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_32_mul_integer z


theorem pow4_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_16 z * pow4_16 z = pow4_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_32_mul z


theorem pow4_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 32 = pow4_32 z := by
  calc
    _ = u3 z ^ 16 * u3 z ^ 16 := by ring
    _ = pow4_16 z * pow4_16 z := by rw [pow4_16_pow z hz]
    _ = _ := pow4_32_root z hz


def pow4_64 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (29 + z * (2 + z * (2 + z * (17 + z * (109 + z * (79 + z * (110 + z * (82 + z * (8 + z * (115 + z * (90 + z * (48 + z * (73 + z * (72 + z * (117 + z * (51 + z * (23 + z * (10 + z * 92)))))))))))))))))))

def pow4_64_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (32 + z * (68 + z * (42 + z * (20 + z * (14 + z * (46 + z * (123 + z * (46 + z * (84 + z * (93 + z * (15 + z * (125 + z * (41 + z * (21 + z * (26 + z * (45 + z * (86 + z * 33))))))))))))))))))

def pow4_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * ((-39) + z * (9 + z * ((-36) + z * (60 + z * (33 + z * (86 + z * (128 + z * (36 + z * (120 + z * (127 + z * ((-58) + z * (145 + z * ((-11) + z * (90 + z * (186 + z * (48 + z * (299 + z * (77 + z * (257 + z * (305 + z * (177 + z * (391 + z * (225 + z * (241 + z * (201 + z * (58 + z * (255 + z * (89 + z * (190 + z * (273 + z * (197 + z * (216 + z * (129 + z * (176 + z * (133 + z * (128 + z * (76 + z * 32))))))))))))))))))))))))))))))))))))))

theorem pow4_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_32 z * pow4_32 z = pow4_64_q z * f z + pow4_64 z + (131 : R) * pow4_64_mul_t z := by
  simp only [pow4_32, pow4_64_q, f, pow4_64, pow4_64_mul_t]
  
  ring

theorem pow4_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_32 z * pow4_32 z = pow4_64_q z * f z + pow4_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_64_mul_integer z


theorem pow4_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_32 z * pow4_32 z = pow4_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_64_mul z


theorem pow4_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 64 = pow4_64 z := by
  calc
    _ = u3 z ^ 32 * u3 z ^ 32 := by ring
    _ = pow4_32 z * pow4_32 z := by rw [pow4_32_pow z hz]
    _ = _ := pow4_64_root z hz


def pow4_65 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (114 + z * (127 + z * (120 + z * (129 + z * (89 + z * (83 + z * (113 + z * (27 + z * (110 + z * (64 + z * (1 + z * (38 + z * (84 + z * (107 + z * (26 + z * (33 + z * (123 + z * (100 + z * 33)))))))))))))))))))

def pow4_65_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (7 + z * (39 + z * (71 + z * (92 + z * (17 + z * (58 + z * (64 + z * (30 + z * (58 + z * (71 + z * (126 + z * (90 + z * (42 + z * (70 + z * (40 + z * (114 + z * (80 + z * 68))))))))))))))))))

def pow4_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-10) + z * ((-50) + z * ((-32) + z * ((-89) + z * ((-57) + z * (10 + z * ((-8) + z * ((-15) + z * ((-28) + z * (143 + z * ((-71) + z * ((-89) + z * (9 + z * (21 + z * ((-14) + z * (30 + z * (67 + z * ((-30) + z * ((-12) + z * ((-46) + z * ((-27) + z * (30 + z * ((-28) + z * (114 + z * (29 + z * (54 + z * ((-24) + z * ((-11) + z * ((-91) + z * (13 + z * (33 + z * (31 + z * ((-39) + z * ((-27) + z * ((-42) + z * (6 + z * (0 + z * 36))))))))))))))))))))))))))))))))))))))

theorem pow4_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_64 z * u3 z = pow4_65_q z * f z + pow4_65 z + (131 : R) * pow4_65_mul_t z := by
  simp only [pow4_64, u3, pow4_65_q, f, pow4_65, pow4_65_mul_t]
  simp only [pow3_131]
  ring

theorem pow4_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_64 z * u3 z = pow4_65_q z * f z + pow4_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_65_mul_integer z


theorem pow4_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_64 z * u3 z = pow4_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_65_mul z


theorem pow4_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 65 = pow4_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow4_64_pow z hz]
  exact pow4_65_root z hz


def pow4_130 {R : Type*} [CommRing R] (z : R) : R := (91 + z * (121 + z * (12 + z * (4 + z * (26 + z * (113 + z * (43 + z * (23 + z * (3 + z * (37 + z * (121 + z * (41 + z * (63 + z * (124 + z * (35 + z * (31 + z * (119 + z * (44 + z * (57 + z * 43)))))))))))))))))))

def pow4_130_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (87 + z * (35 + z * (54 + z * (88 + z * (119 + z * (70 + z * (83 + z * (67 + z * (32 + z * (9 + z * (27 + z * (7 + z * (62 + z * (127 + z * (105 + z * (128 + z * (95 + z * 41))))))))))))))))))

def pow4_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-49) + z * (33 + z * (141 + z * (222 + z * (255 + z * (301 + z * (337 + z * (354 + z * (259 + z * (373 + z * (397 + z * (185 + z * (175 + z * (238 + z * (257 + z * (204 + z * (138 + z * (237 + z * (365 + z * (360 + z * (312 + z * (214 + z * (212 + z * (97 + z * ((-45) + z * (56 + z * (94 + z * (1 + z * ((-85) + z * (33 + z * (148 + z * (22 + z * ((-78) + z * (5 + z * (81 + z * (71 + z * (29 + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow4_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_65 z * pow4_65 z = pow4_130_q z * f z + pow4_130 z + (131 : R) * pow4_130_mul_t z := by
  simp only [pow4_65, pow4_130_q, f, pow4_130, pow4_130_mul_t]
  
  ring

theorem pow4_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_65 z * pow4_65 z = pow4_130_q z * f z + pow4_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_130_mul_integer z


theorem pow4_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_65 z * pow4_65 z = pow4_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_130_mul z


theorem pow4_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 130 = pow4_130 z := by
  calc
    _ = u3 z ^ 65 * u3 z ^ 65 := by ring
    _ = pow4_65 z * pow4_65 z := by rw [pow4_65_pow z hz]
    _ = _ := pow4_130_root z hz


def pow4_131 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (64 + z * (118 + z * (110 + z * (94 + z * (110 + z * (101 + z * (49 + z * (27 + z * (29 + z * (42 + z * (109 + z * (72 + z * (115 + z * (113 + z * (23 + z * (53 + z * (52 + z * (32 + z * 22)))))))))))))))))))

def pow4_131_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (128 + z * (111 + z * (24 + z * (66 + z * (110 + z * (17 + z * (118 + z * (89 + z * (24 + z * (112 + z * (56 + z * (108 + z * (0 + z * (8 + z * (49 + z * (107 + z * (70 + z * 9))))))))))))))))))

def pow4_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (36 + z * (38 + z * ((-62) + z * (6 + z * ((-7) + z * ((-67) + z * ((-78) + z * ((-109) + z * ((-125) + z * ((-182) + z * ((-14) + z * ((-65) + z * ((-205) + z * ((-110) + z * ((-82) + z * ((-101) + z * (13 + z * ((-118) + z * ((-81) + z * ((-49) + z * ((-160) + z * ((-39) + z * (143 + z * ((-101) + z * ((-29) + z * (64 + z * (19 + z * (72 + z * (36 + z * (75 + z * (106 + z * (71 + z * (62 + z * (41 + z * (21 + z * (33 + z * (27 + z * (32 + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow4_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_130 z * u3 z = pow4_131_q z * f z + pow4_131 z + (131 : R) * pow4_131_mul_t z := by
  simp only [pow4_130, u3, pow4_131_q, f, pow4_131, pow4_131_mul_t]
  simp only [pow3_131]
  ring

theorem pow4_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow4_130 z * u3 z = pow4_131_q z * f z + pow4_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow4_131_mul_integer z


theorem pow4_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow4_130 z * u3 z = pow4_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_131_mul z


theorem pow4_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u3 z ^ 131 = pow4_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow4_130_pow z hz]
  exact pow4_131_root z hz


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_131 z

theorem iterate4 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 4) = u4 z := by
  calc
    _ = (z ^ (131 ^ 3)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u3 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate3 z hz)
    _ = _ := pow4_131_pow z hz

end DimensionTen.Mod131

end

end OAI
