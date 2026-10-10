import OAI.Analysis.Quantum.DimensionTen.Mod131Powers02

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow5_2 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (86 + z * (104 + z * (127 + z * (85 + z * (123 + z * (112 + z * (80 + z * (0 + z * (74 + z * (115 + z * (65 + z * (13 + z * (25 + z * (125 + z * (71 + z * (52 + z * (44 + z * (127 + z * 63)))))))))))))))))))

def pow5_2_q {R : Type*} [CommRing R] (z : R) : R := (100 + z * (19 + z * (61 + z * (54 + z * (127 + z * (16 + z * (7 + z * (8 + z * (59 + z * (22 + z * (83 + z * (51 + z * (120 + z * (40 + z * (110 + z * (13 + z * (111 + z * (118 + z * 91))))))))))))))))))

def pow5_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * (8 + z * (47 + z * (134 + z * (134 + z * (192 + z * (319 + z * (322 + z * (269 + z * (222 + z * (244 + z * (160 + z * (123 + z * (231 + z * (359 + z * (308 + z * (358 + z * (337 + z * (309 + z * (180 + z * (141 + z * ((-34) + z * (14 + z * ((-28) + z * (84 + z * ((-18) + z * ((-3) + z * (4 + z * ((-47) + z * ((-133) + z * ((-47) + z * ((-31) + z * ((-53) + z * ((-115) + z * ((-107) + z * ((-100) + z * ((-76) + z * ((-36) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow5_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z + (131 : R) * pow5_2_mul_t z := by
  simp only [u4, pow5_2_q, f, pow5_2, pow5_2_mul_t]
  simp only [pow4_131]
  ring

theorem pow5_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_2_mul_integer z


theorem pow5_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z * u4 z = pow5_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_2_mul z


theorem pow5_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 2 = pow5_2 z := by
  calc
    _ = u4 z ^ 1 * u4 z ^ 1 := by ring
    _ = u4 z * u4 z := by simp only [pow_one]
    _ = _ := pow5_2_root z hz


def pow5_4 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (55 + z * (94 + z * (128 + z * (73 + z * (110 + z * (64 + z * (50 + z * (77 + z * (127 + z * (80 + z * (51 + z * (18 + z * (64 + z * (21 + z * (73 + z * (29 + z * (99 + z * (80 + z * 6)))))))))))))))))))

def pow5_4_q {R : Type*} [CommRing R] (z : R) : R := (97 + z * (63 + z * (5 + z * (78 + z * (43 + z * (63 + z * (124 + z * (114 + z * (43 + z * (16 + z * (11 + z * (14 + z * (99 + z * (28 + z * (42 + z * (92 + z * (82 + z * (66 + z * 39))))))))))))))))))

def pow5_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-12) + z * (41 + z * (126 + z * (185 + z * (183 + z * (317 + z * (325 + z * (248 + z * (281 + z * (318 + z * (244 + z * (271 + z * (242 + z * (186 + z * (304 + z * (323 + z * (237 + z * (215 + z * (339 + z * (510 + z * (520 + z * (216 + z * (199 + z * (312 + z * (200 + z * (25 + z * (80 + z * (230 + z * (191 + z * (58 + z * (13 + z * (192 + z * (145 + z * (50 + z * (49 + z * (114 + z * (102 + z * 30))))))))))))))))))))))))))))))))))))))

theorem pow5_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z + (131 : R) * pow5_4_mul_t z := by
  simp only [pow5_2, pow5_4_q, f, pow5_4, pow5_4_mul_t]
  
  ring

theorem pow5_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_4_mul_integer z


theorem pow5_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_2 z * pow5_2 z = pow5_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_4_mul z


theorem pow5_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 4 = pow5_4 z := by
  calc
    _ = u4 z ^ 2 * u4 z ^ 2 := by ring
    _ = pow5_2 z * pow5_2 z := by rw [pow5_2_pow z hz]
    _ = _ := pow5_4_root z hz


def pow5_8 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (115 + z * (125 + z * (69 + z * (87 + z * (40 + z * (120 + z * (107 + z * (108 + z * (115 + z * (3 + z * (34 + z * (57 + z * (57 + z * (128 + z * (126 + z * (97 + z * (78 + z * (21 + z * 1)))))))))))))))))))

def pow5_8_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (111 + z * (61 + z * (30 + z * (26 + z * (9 + z * (124 + z * (94 + z * (5 + z * (40 + z * (4 + z * (126 + z * (121 + z * (12 + z * (5 + z * (38 + z * (15 + z * (25 + z * 36))))))))))))))))))

def pow5_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (86 + z * (41 + z * (107 + z * (208 + z * (214 + z * (310 + z * (234 + z * (263 + z * (300 + z * (361 + z * (395 + z * (318 + z * (287 + z * (305 + z * (202 + z * (309 + z * (215 + z * (274 + z * (397 + z * (209 + z * (277 + z * (339 + z * (179 + z * (86 + z * (102 + z * (89 + z * (226 + z * (147 + z * (58 + z * ((-24) + z * ((-2) + z * (23 + z * (106 + z * (83 + z * (58 + z * (91 + z * (29 + z * ((-11) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow5_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z + (131 : R) * pow5_8_mul_t z := by
  simp only [pow5_4, pow5_8_q, f, pow5_8, pow5_8_mul_t]
  
  ring

theorem pow5_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_8_mul_integer z


theorem pow5_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_4 z * pow5_4 z = pow5_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_8_mul z


theorem pow5_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 8 = pow5_8 z := by
  calc
    _ = u4 z ^ 4 * u4 z ^ 4 := by ring
    _ = pow5_4 z * pow5_4 z := by rw [pow5_4_pow z hz]
    _ = _ := pow5_8_root z hz


def pow5_16 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (96 + z * (50 + z * (88 + z * (93 + z * (27 + z * (50 + z * (124 + z * (106 + z * (121 + z * (125 + z * (108 + z * (3 + z * (24 + z * (47 + z * (21 + z * (25 + z * (106 + z * (26 + z * 105)))))))))))))))))))

def pow5_16_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (119 + z * (54 + z * (22 + z * (73 + z * (13 + z * (59 + z * (71 + z * (94 + z * (108 + z * (93 + z * (10 + z * (103 + z * (18 + z * (87 + z * (108 + z * (26 + z * (107 + z * 1))))))))))))))))))

def pow5_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (162 + z * (258 + z * (260 + z * (299 + z * (199 + z * (310 + z * (432 + z * (472 + z * (467 + z * (411 + z * (281 + z * (177 + z * (257 + z * (395 + z * (627 + z * (625 + z * (450 + z * (475 + z * (185 + z * (232 + z * (334 + z * (298 + z * (347 + z * (229 + z * (6 + z * ((-20) + z * ((-13) + z * (9 + z * (191 + z * (186 + z * (181 + z * (127 + z * ((-15) + z * ((-28) + z * ((-36) + z * ((-50) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow5_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z + (131 : R) * pow5_16_mul_t z := by
  simp only [pow5_8, pow5_16_q, f, pow5_16, pow5_16_mul_t]
  
  ring

theorem pow5_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_16_mul_integer z


theorem pow5_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_8 z * pow5_8 z = pow5_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_16_mul z


theorem pow5_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 16 = pow5_16 z := by
  calc
    _ = u4 z ^ 8 * u4 z ^ 8 := by ring
    _ = pow5_8 z * pow5_8 z := by rw [pow5_8_pow z hz]
    _ = _ := pow5_16_root z hz


def pow5_32 {R : Type*} [CommRing R] (z : R) : R := (91 + z * (125 + z * (56 + z * (51 + z * (96 + z * (112 + z * (11 + z * (91 + z * (73 + z * (111 + z * (91 + z * (122 + z * (110 + z * (6 + z * (68 + z * (1 + z * (110 + z * (118 + z * (104 + z * 64)))))))))))))))))))

def pow5_32_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (9 + z * (18 + z * (35 + z * (81 + z * (122 + z * (37 + z * (68 + z * (52 + z * (33 + z * (22 + z * (71 + z * (75 + z * (106 + z * (66 + z * (53 + z * (10 + z * (13 + z * 21))))))))))))))))))

def pow5_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (76 + z * (67 + z * (140 + z * (149 + z * (36 + z * (110 + z * (166 + z * (205 + z * (236 + z * (423 + z * (439 + z * (255 + z * (185 + z * (334 + z * (200 + z * (62 + z * (347 + z * (364 + z * (320 + z * (335 + z * (234 + z * (98 + z * (58 + z * (94 + z * (161 + z * (242 + z * (264 + z * (256 + z * (77 + z * (45 + z * ((-63) + z * ((-19) + z * (48 + z * (79 + z * (63 + z * (159 + z * (31 + z * 84))))))))))))))))))))))))))))))))))))))

theorem pow5_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_16 z * pow5_16 z = pow5_32_q z * f z + pow5_32 z + (131 : R) * pow5_32_mul_t z := by
  simp only [pow5_16, pow5_32_q, f, pow5_32, pow5_32_mul_t]
  
  ring

theorem pow5_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_16 z * pow5_16 z = pow5_32_q z * f z + pow5_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_32_mul_integer z


theorem pow5_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_16 z * pow5_16 z = pow5_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_32_mul z


theorem pow5_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 32 = pow5_32 z := by
  calc
    _ = u4 z ^ 16 * u4 z ^ 16 := by ring
    _ = pow5_16 z * pow5_16 z := by rw [pow5_16_pow z hz]
    _ = _ := pow5_32_root z hz


def pow5_64 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (25 + z * (101 + z * (98 + z * (2 + z * (95 + z * (98 + z * (43 + z * (71 + z * (95 + z * (20 + z * (80 + z * (13 + z * (92 + z * (118 + z * (50 + z * (50 + z * (4 + z * (66 + z * 21)))))))))))))))))))

def pow5_64_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (58 + z * (52 + z * (40 + z * (91 + z * (74 + z * (70 + z * (72 + z * (17 + z * (3 + z * (32 + z * (73 + z * (107 + z * (28 + z * (12 + z * (78 + z * (14 + z * (129 + z * 35))))))))))))))))))

def pow5_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (109 + z * (98 + z * (94 + z * (106 + z * (158 + z * (145 + z * (82 + z * (156 + z * (248 + z * (345 + z * (289 + z * (397 + z * (298 + z * (349 + z * (266 + z * (333 + z * (393 + z * (500 + z * (514 + z * (423 + z * (592 + z * (325 + z * (347 + z * (252 + z * (297 + z * (406 + z * (421 + z * (397 + z * (254 + z * (194 + z * (87 + z * (111 + z * (125 + z * (165 + z * (216 + z * (117 + z * (83 + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow5_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_32 z * pow5_32 z = pow5_64_q z * f z + pow5_64 z + (131 : R) * pow5_64_mul_t z := by
  simp only [pow5_32, pow5_64_q, f, pow5_64, pow5_64_mul_t]
  
  ring

theorem pow5_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_32 z * pow5_32 z = pow5_64_q z * f z + pow5_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_64_mul_integer z


theorem pow5_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_32 z * pow5_32 z = pow5_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_64_mul z


theorem pow5_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 64 = pow5_64 z := by
  calc
    _ = u4 z ^ 32 * u4 z ^ 32 := by ring
    _ = pow5_32 z * pow5_32 z := by rw [pow5_32_pow z hz]
    _ = _ := pow5_64_root z hz


def pow5_65 {R : Type*} [CommRing R] (z : R) : R := (64 + z * (50 + z * (102 + z * (11 + z * (97 + z * (61 + z * (88 + z * (18 + z * (38 + z * (71 + z * (46 + z * (8 + z * (28 + z * (81 + z * (58 + z * (7 + z * (56 + z * (105 + z * (77 + z * 103)))))))))))))))))))

def pow5_65_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (1 + z * (78 + z * (114 + z * (10 + z * (84 + z * (14 + z * (46 + z * (71 + z * (126 + z * (19 + z * (56 + z * (2 + z * (114 + z * (45 + z * (3 + z * (43 + z * (59 + z * 69))))))))))))))))))

def pow5_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (17 + z * (38 + z * (57 + z * (88 + z * (135 + z * (177 + z * (135 + z * (214 + z * (186 + z * (78 + z * (170 + z * (180 + z * (127 + z * (143 + z * (233 + z * (267 + z * (263 + z * (127 + z * (299 + z * (176 + z * (18 + z * (70 + z * (130 + z * (46 + z * (34 + z * (9 + z * (104 + z * (56 + z * ((-12) + z * (26 + z * (46 + z * (33 + z * ((-16) + z * ((-36) + z * ((-30) + z * ((-36) + z * ((-19) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow5_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_64 z * u4 z = pow5_65_q z * f z + pow5_65 z + (131 : R) * pow5_65_mul_t z := by
  simp only [pow5_64, u4, pow5_65_q, f, pow5_65, pow5_65_mul_t]
  simp only [pow4_131]
  ring

theorem pow5_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_64 z * u4 z = pow5_65_q z * f z + pow5_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_65_mul_integer z


theorem pow5_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_64 z * u4 z = pow5_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_65_mul z


theorem pow5_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 65 = pow5_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow5_64_pow z hz]
  exact pow5_65_root z hz


def pow5_130 {R : Type*} [CommRing R] (z : R) : R := (122 + z * (100 + z * (1 + z * (30 + z * (108 + z * (50 + z * (56 + z * (120 + z * (21 + z * (52 + z * (86 + z * (35 + z * (0 + z * (120 + z * (56 + z * (0 + z * (73 + z * (66 + z * (79 + z * 74)))))))))))))))))))

def pow5_130_q {R : Type*} [CommRing R] (z : R) : R := (69 + z * (69 + z * (116 + z * (47 + z * (15 + z * (74 + z * (0 + z * (0 + z * (72 + z * (48 + z * (124 + z * (112 + z * (7 + z * (21 + z * (59 + z * (95 + z * (30 + z * (12 + z * 129))))))))))))))))))

def pow5_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-3) + z * (16 + z * ((-17) + z * (53 + z * ((-24) + z * (118 + z * ((-8) + z * (89 + z * ((-10) + z * (4 + z * ((-18) + z * ((-93) + z * ((-148) + z * ((-6) + z * ((-79) + z * ((-131) + z * ((-11) + z * (0 + z * (48 + z * ((-22) + z * (50 + z * ((-9) + z * (64 + z * (53 + z * (55 + z * ((-104) + z * ((-60) + z * ((-2) + z * ((-89) + z * ((-1) + z * (55 + z * (128 + z * (61 + z * (10 + z * (142 + z * (146 + z * (56 + z * 80))))))))))))))))))))))))))))))))))))))

theorem pow5_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_65 z * pow5_65 z = pow5_130_q z * f z + pow5_130 z + (131 : R) * pow5_130_mul_t z := by
  simp only [pow5_65, pow5_130_q, f, pow5_130, pow5_130_mul_t]
  
  ring

theorem pow5_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_65 z * pow5_65 z = pow5_130_q z * f z + pow5_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_130_mul_integer z


theorem pow5_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_65 z * pow5_65 z = pow5_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_130_mul z


theorem pow5_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 130 = pow5_130 z := by
  calc
    _ = u4 z ^ 65 * u4 z ^ 65 := by ring
    _ = pow5_65 z * pow5_65 z := by rw [pow5_65_pow z hz]
    _ = _ := pow5_130_root z hz


def pow5_131 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (89 + z * (102 + z * (35 + z * (36 + z * (105 + z * (54 + z * (56 + z * (65 + z * (52 + z * (11 + z * (41 + z * (74 + z * (91 + z * (104 + z * (46 + z * (29 + z * (36 + z * (95 + z * 75)))))))))))))))))))

def pow5_131_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (25 + z * (61 + z * (110 + z * (123 + z * (98 + z * (76 + z * (52 + z * (11 + z * (115 + z * (73 + z * (13 + z * (115 + z * (12 + z * (81 + z * (12 + z * (127 + z * (17 + z * 56))))))))))))))))))

def pow5_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (36 + z * (78 + z * (110 + z * (123 + z * (92 + z * (86 + z * (149 + z * (109 + z * (46 + z * (70 + z * (86 + z * (80 + z * (95 + z * (119 + z * (23 + z * (100 + z * (6 + z * (20 + z * (148 + z * (128 + z * (75 + z * (9 + z * (29 + z * (0 + z * (110 + z * ((-65) + z * (36 + z * (12 + z * ((-41) + z * (18 + z * (129 + z * (60 + z * (69 + z * (22 + z * ((-18) + z * ((-3) + z * (25 + z * (3 + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow5_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_130 z * u4 z = pow5_131_q z * f z + pow5_131 z + (131 : R) * pow5_131_mul_t z := by
  simp only [pow5_130, u4, pow5_131_q, f, pow5_131, pow5_131_mul_t]
  simp only [pow4_131]
  ring

theorem pow5_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow5_130 z * u4 z = pow5_131_q z * f z + pow5_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow5_131_mul_integer z


theorem pow5_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow5_130 z * u4 z = pow5_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_131_mul z


theorem pow5_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u4 z ^ 131 = pow5_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow5_130_pow z hz]
  exact pow5_131_root z hz


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_131 z

theorem iterate5 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 5) = u5 z := by
  calc
    _ = (z ^ (131 ^ 4)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u4 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate4 z hz)
    _ = _ := pow5_131_pow z hz


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (22 + z * (30 + z * (4 + z * (71 + z * (62 + z * (85 + z * (43 + z * (123 + z * (9 + z * (87 + z * (105 + z * (8 + z * (62 + z * (54 + z * (19 + z * (26 + z * (25 + z * (39 + z * 93)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (66 + z * (81 + z * (103 + z * (75 + z * (94 + z * (12 + z * (7 + z * (74 + z * (105 + z * (14 + z * (17 + z * (43 + z * (39 + z * (99 + z * (2 + z * (41 + z * (106 + z * 123))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * (75 + z * (113 + z * (74 + z * (11 + z * (14 + z * (94 + z * (95 + z * (29 + z * (17 + z * (5 + z * ((-30) + z * ((-16) + z * (30 + z * (161 + z * (171 + z * (2 + z * (9 + z * (103 + z * (167 + z * (132 + z * ((-6) + z * ((-65) + z * (86 + z * (100 + z * ((-36) + z * (77 + z * (95 + z * (29 + z * ((-61) + z * (14 + z * (127 + z * (158 + z * (31 + z * ((-36) + z * ((-29) + z * (1 + z * (46 + z * 42))))))))))))))))))))))))))))))))))))))

theorem pow6_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z + (131 : R) * pow6_2_mul_t z := by
  simp only [u5, pow6_2_q, f, pow6_2, pow6_2_mul_t]
  simp only [pow5_131]
  ring

theorem pow6_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_2_mul_integer z


theorem pow6_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z * u5 z = pow6_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_2_mul z


theorem pow6_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 2 = pow6_2 z := by
  calc
    _ = u5 z ^ 1 * u5 z ^ 1 := by ring
    _ = u5 z * u5 z := by simp only [pow_one]
    _ = _ := pow6_2_root z hz


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (82 + z * (8 + z * (44 + z * (82 + z * (53 + z * (128 + z * (71 + z * (103 + z * (22 + z * (72 + z * (33 + z * (9 + z * (54 + z * (127 + z * (14 + z * (97 + z * (83 + z * (33 + z * 8)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (8 + z * (40 + z * (120 + z * (49 + z * (31 + z * (30 + z * (123 + z * (52 + z * (22 + z * (112 + z * (36 + z * (107 + z * (76 + z * (87 + z * (49 + z * (108 + z * (113 + z * 3))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (22 + z * (4 + z * ((-4) + z * ((-58) + z * ((-22) + z * ((-46) + z * (49 + z * ((-98) + z * ((-25) + z * ((-57) + z * (33 + z * ((-60) + z * ((-80) + z * ((-1) + z * ((-81) + z * ((-163) + z * ((-71) + z * ((-153) + z * ((-147) + z * ((-97) + z * ((-216) + z * ((-168) + z * ((-186) + z * ((-151) + z * ((-76) + z * ((-150) + z * ((-152) + z * ((-23) + z * ((-223) + z * ((-100) + z * ((-39) + z * ((-115) + z * ((-67) + z * ((-84) + z * ((-71) + z * ((-55) + z * ((-12) + z * (53 + z * 66))))))))))))))))))))))))))))))))))))))

theorem pow6_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z + (131 : R) * pow6_4_mul_t z := by
  simp only [pow6_2, pow6_4_q, f, pow6_4, pow6_4_mul_t]
  
  ring

theorem pow6_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_4_mul_integer z


theorem pow6_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_2 z * pow6_2 z = pow6_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_4_mul z


theorem pow6_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 4 = pow6_4 z := by
  calc
    _ = u5 z ^ 2 * u5 z ^ 2 := by ring
    _ = pow6_2 z * pow6_2 z := by rw [pow6_2_pow z hz]
    _ = _ := pow6_4_root z hz


def pow6_8 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (49 + z * (75 + z * (84 + z * (106 + z * (117 + z * (17 + z * (56 + z * (77 + z * (126 + z * (36 + z * (16 + z * (73 + z * (100 + z * (70 + z * (101 + z * (36 + z * (47 + z * (78 + z * 48)))))))))))))))))))

def pow6_8_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (33 + z * (60 + z * (1 + z * (119 + z * (94 + z * (124 + z * (57 + z * (4 + z * (121 + z * (122 + z * (67 + z * (98 + z * (128 + z * (53 + z * (127 + z * (96 + z * (103 + z * 64))))))))))))))))))

def pow6_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-18) + z * (6 + z * ((-31) + z * ((-35) + z * ((-17) + z * ((-106) + z * (26 + z * ((-5) + z * ((-28) + z * ((-44) + z * ((-26) + z * ((-12) + z * ((-168) + z * ((-95) + z * ((-124) + z * ((-183) + z * ((-292) + z * ((-207) + z * ((-149) + z * ((-124) + z * ((-197) + z * ((-142) + z * ((-207) + z * ((-88) + z * ((-263) + z * ((-265) + z * ((-149) + z * ((-252) + z * ((-271) + z * ((-38) + z * ((-71) + z * ((-72) + z * ((-61) + z * ((-85) + z * ((-66) + z * ((-63) + z * ((-29) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow6_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z + (131 : R) * pow6_8_mul_t z := by
  simp only [pow6_4, pow6_8_q, f, pow6_8, pow6_8_mul_t]
  
  ring

theorem pow6_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_8_mul_integer z


theorem pow6_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_4 z * pow6_4 z = pow6_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_8_mul z


theorem pow6_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 8 = pow6_8 z := by
  calc
    _ = u5 z ^ 4 * u5 z ^ 4 := by ring
    _ = pow6_4 z * pow6_4 z := by rw [pow6_4_pow z hz]
    _ = _ := pow6_8_root z hz


def pow6_16 {R : Type*} [CommRing R] (z : R) : R := (62 + z * (113 + z * (23 + z * (105 + z * (26 + z * (88 + z * (123 + z * (86 + z * (40 + z * (13 + z * (51 + z * (47 + z * (114 + z * (78 + z * (49 + z * (121 + z * (68 + z * (2 + z * (101 + z * 26)))))))))))))))))))

def pow6_16_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (113 + z * (64 + z * (75 + z * (18 + z * (78 + z * (7 + z * (19 + z * (44 + z * (10 + z * (92 + z * (53 + z * (53 + z * (21 + z * (24 + z * (55 + z * (3 + z * (48 + z * 77))))))))))))))))))

def pow6_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-59) + z * ((-67) + z * ((-57) + z * ((-1) + z * ((-7) + z * (76 + z * (110 + z * (87 + z * (108 + z * (110 + z * (159 + z * (92 + z * (127 + z * (170 + z * (121 + z * (243 + z * (342 + z * (303 + z * (202 + z * (276 + z * (306 + z * (337 + z * (254 + z * (261 + z * (171 + z * (155 + z * (258 + z * (183 + z * (46 + z * (118 + z * (148 + z * (177 + z * (106 + z * (36 + z * (30 + z * (22 + z * (18 + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow6_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z + (131 : R) * pow6_16_mul_t z := by
  simp only [pow6_8, pow6_16_q, f, pow6_16, pow6_16_mul_t]
  
  ring

theorem pow6_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_16_mul_integer z


theorem pow6_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_8 z * pow6_8 z = pow6_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_16_mul z


theorem pow6_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 16 = pow6_16 z := by
  calc
    _ = u5 z ^ 8 * u5 z ^ 8 := by ring
    _ = pow6_8 z * pow6_8 z := by rw [pow6_8_pow z hz]
    _ = _ := pow6_16_root z hz


def pow6_32 {R : Type*} [CommRing R] (z : R) : R := (95 + z * (18 + z * (96 + z * (113 + z * (123 + z * (25 + z * (123 + z * (91 + z * (118 + z * (40 + z * (85 + z * (28 + z * (69 + z * (87 + z * (58 + z * (114 + z * (27 + z * (43 + z * (57 + z * 123)))))))))))))))))))

def pow6_32_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (121 + z * (88 + z * (104 + z * (52 + z * (87 + z * (36 + z * (83 + z * (121 + z * (84 + z * (122 + z * (56 + z * (90 + z * (5 + z * (44 + z * (42 + z * (59 + z * (67 + z * 21))))))))))))))))))

def pow6_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * (14 + z * ((-22) + z * ((-15) + z * (17 + z * ((-132) + z * (117 + z * (65 + z * ((-18) + z * ((-66) + z * ((-106) + z * ((-79) + z * ((-125) + z * (0 + z * ((-90) + z * (22 + z * (17 + z * ((-37) + z * (136 + z * (70 + z * ((-38) + z * (81 + z * (41 + z * (3 + z * (85 + z * (80 + z * (19 + z * (25 + z * (59 + z * (32 + z * (191 + z * (168 + z * (48 + z * (95 + z * (66 + z * ((-38) + z * (35 + z * (29 + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow6_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_16 z * pow6_16 z = pow6_32_q z * f z + pow6_32 z + (131 : R) * pow6_32_mul_t z := by
  simp only [pow6_16, pow6_32_q, f, pow6_32, pow6_32_mul_t]
  
  ring

theorem pow6_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_16 z * pow6_16 z = pow6_32_q z * f z + pow6_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_32_mul_integer z


theorem pow6_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_16 z * pow6_16 z = pow6_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_32_mul z


theorem pow6_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 32 = pow6_32 z := by
  calc
    _ = u5 z ^ 16 * u5 z ^ 16 := by ring
    _ = pow6_16 z * pow6_16 z := by rw [pow6_16_pow z hz]
    _ = _ := pow6_32_root z hz


def pow6_64 {R : Type*} [CommRing R] (z : R) : R := (52 + z * (96 + z * (108 + z * (119 + z * (38 + z * (64 + z * (31 + z * (106 + z * (2 + z * (0 + z * (9 + z * (76 + z * (113 + z * (70 + z * (100 + z * (84 + z * (74 + z * (27 + z * (89 + z * 90)))))))))))))))))))

def pow6_64_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (76 + z * (121 + z * (93 + z * (61 + z * (38 + z * (94 + z * (95 + z * (5 + z * (3 + z * (6 + z * (56 + z * (77 + z * (6 + z * (74 + z * (89 + z * (43 + z * (104 + z * 64))))))))))))))))))

def pow6_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (33 + z * ((-37) + z * (22 + z * (57 + z * (100 + z * (10 + z * (234 + z * (108 + z * (219 + z * (181 + z * (407 + z * (138 + z * (284 + z * (230 + z * (276 + z * (304 + z * (317 + z * (299 + z * (278 + z * (292 + z * (229 + z * (517 + z * (322 + z * (319 + z * (155 + z * (312 + z * (199 + z * (276 + z * (111 + z * (130 + z * (49 + z * (107 + z * (163 + z * (46 + z * (106 + z * ((-5) + z * (24 + z * (74 + z * 115))))))))))))))))))))))))))))))))))))))

theorem pow6_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_32 z * pow6_32 z = pow6_64_q z * f z + pow6_64 z + (131 : R) * pow6_64_mul_t z := by
  simp only [pow6_32, pow6_64_q, f, pow6_64, pow6_64_mul_t]
  
  ring

theorem pow6_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_32 z * pow6_32 z = pow6_64_q z * f z + pow6_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_64_mul_integer z


theorem pow6_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_32 z * pow6_32 z = pow6_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_64_mul z


theorem pow6_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 64 = pow6_64 z := by
  calc
    _ = u5 z ^ 32 * u5 z ^ 32 := by ring
    _ = pow6_32 z * pow6_32 z := by rw [pow6_32_pow z hz]
    _ = _ := pow6_64_root z hz


def pow6_65 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (38 + z * (58 + z * (75 + z * (107 + z * (91 + z * (121 + z * (125 + z * (102 + z * (99 + z * (8 + z * (121 + z * (104 + z * (56 + z * (43 + z * (111 + z * (68 + z * (101 + z * (49 + z * 109)))))))))))))))))))

def pow6_65_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (24 + z * (108 + z * (109 + z * (18 + z * (88 + z * (74 + z * (12 + z * (1 + z * (82 + z * (86 + z * (97 + z * (106 + z * (99 + z * (115 + z * (37 + z * (56 + z * (60 + z * 69))))))))))))))))))

def pow6_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * (64 + z * (90 + z * (143 + z * (77 + z * (53 + z * (87 + z * (59 + z * (81 + z * (71 + z * ((-86) + z * ((-121) + z * (56 + z * ((-50) + z * ((-23) + z * (82 + z * (65 + z * ((-4) + z * ((-61) + z * (96 + z * (163 + z * ((-11) + z * ((-180) + z * ((-65) + z * (3 + z * ((-33) + z * (34 + z * ((-8) + z * ((-32) + z * ((-49) + z * (49 + z * (96 + z * (121 + z * (92 + z * (48 + z * (25 + z * (43 + z * (81 + z * 51))))))))))))))))))))))))))))))))))))))

theorem pow6_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_64 z * u5 z = pow6_65_q z * f z + pow6_65 z + (131 : R) * pow6_65_mul_t z := by
  simp only [pow6_64, u5, pow6_65_q, f, pow6_65, pow6_65_mul_t]
  simp only [pow5_131]
  ring

theorem pow6_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_64 z * u5 z = pow6_65_q z * f z + pow6_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_65_mul_integer z


theorem pow6_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_64 z * u5 z = pow6_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_65_mul z


theorem pow6_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 65 = pow6_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow6_64_pow z hz]
  exact pow6_65_root z hz


def pow6_130 {R : Type*} [CommRing R] (z : R) : R := (70 + z * (81 + z * (34 + z * (78 + z * (109 + z * (51 + z * (97 + z * (129 + z * (32 + z * (3 + z * (114 + z * (85 + z * (1 + z * (117 + z * (120 + z * (71 + z * (124 + z * (82 + z * (71 + z * 63)))))))))))))))))))

def pow6_130_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (124 + z * (130 + z * (35 + z * (1 + z * (54 + z * (27 + z * (114 + z * (22 + z * (90 + z * (12 + z * (15 + z * (28 + z * (116 + z * (124 + z * (119 + z * (75 + z * (91 + z * 91))))))))))))))))))

def pow6_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-32) + z * ((-58) + z * ((-47) + z * (23 + z * (38 + z * (45 + z * (122 + z * (246 + z * (210 + z * (255 + z * (395 + z * (372 + z * (343 + z * (262 + z * (444 + z * (408 + z * (360 + z * (282 + z * (446 + z * (409 + z * (444 + z * (455 + z * (559 + z * (475 + z * (234 + z * (257 + z * (248 + z * (249 + z * (70 + z * (209 + z * (126 + z * (93 + z * (29 + z * (125 + z * (75 + z * (99 + z * (35 + z * 90))))))))))))))))))))))))))))))))))))))

theorem pow6_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_65 z * pow6_65 z = pow6_130_q z * f z + pow6_130 z + (131 : R) * pow6_130_mul_t z := by
  simp only [pow6_65, pow6_130_q, f, pow6_130, pow6_130_mul_t]
  
  ring

theorem pow6_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_65 z * pow6_65 z = pow6_130_q z * f z + pow6_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_130_mul_integer z


theorem pow6_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_65 z * pow6_65 z = pow6_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_130_mul z


theorem pow6_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 130 = pow6_130 z := by
  calc
    _ = u5 z ^ 65 * u5 z ^ 65 := by ring
    _ = pow6_65 z * pow6_65 z := by rw [pow6_65_pow z hz]
    _ = _ := pow6_130_root z hz


def pow6_131 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (119 + z * (100 + z * (65 + z * (61 + z * (44 + z * (98 + z * (122 + z * (121 + z * (89 + z * (124 + z * (95 + z * (115 + z * (125 + z * (87 + z * (16 + z * (127 + z * (125 + z * (103 + z * 39)))))))))))))))))))

def pow6_131_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (17 + z * (67 + z * (15 + z * (52 + z * (102 + z * (85 + z * (61 + z * (125 + z * (122 + z * (120 + z * (9 + z * (113 + z * (79 + z * (130 + z * (113 + z * (104 + z * (105 + z * 9))))))))))))))))))

def pow6_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * (88 + z * (84 + z * (119 + z * (121 + z * (141 + z * (168 + z * (144 + z * (166 + z * (64 + z * ((-20) + z * (74 + z * (76 + z * ((-25) + z * (6 + z * (126 + z * (69 + z * ((-110) + z * (114 + z * (136 + z * (10 + z * ((-92) + z * (1 + z * ((-28) + z * ((-39) + z * ((-85) + z * ((-85) + z * ((-72) + z * ((-31) + z * (72 + z * (72 + z * (72 + z * (90 + z * (20 + z * (41 + z * (60 + z * (58 + z * (81 + z * 36))))))))))))))))))))))))))))))))))))))

theorem pow6_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_130 z * u5 z = pow6_131_q z * f z + pow6_131 z + (131 : R) * pow6_131_mul_t z := by
  simp only [pow6_130, u5, pow6_131_q, f, pow6_131, pow6_131_mul_t]
  simp only [pow5_131]
  ring

theorem pow6_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow6_130 z * u5 z = pow6_131_q z * f z + pow6_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow6_131_mul_integer z


theorem pow6_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow6_130 z * u5 z = pow6_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_131_mul z


theorem pow6_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u5 z ^ 131 = pow6_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow6_130_pow z hz]
  exact pow6_131_root z hz


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_131 z

theorem iterate6 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 6) = u6 z := by
  calc
    _ = (z ^ (131 ^ 5)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate5 z hz)
    _ = _ := pow6_131_pow z hz

end DimensionTen.Mod131

end

end OAI
