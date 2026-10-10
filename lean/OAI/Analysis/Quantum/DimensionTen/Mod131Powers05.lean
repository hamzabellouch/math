import OAI.Analysis.Quantum.DimensionTen.Mod131Powers04

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow9_2 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (64 + z * (67 + z * (0 + z * (93 + z * (75 + z * (111 + z * (95 + z * (97 + z * (89 + z * (111 + z * (52 + z * (124 + z * (88 + z * (64 + z * (78 + z * (127 + z * (37 + z * (88 + z * 33)))))))))))))))))))

def pow9_2_q {R : Type*} [CommRing R] (z : R) : R := (86 + z * (20 + z * (117 + z * (125 + z * (122 + z * (129 + z * (96 + z * (87 + z * (17 + z * (113 + z * (93 + z * (102 + z * (116 + z * (44 + z * (108 + z * (94 + z * (52 + z * (69 + z * 34))))))))))))))))))

def pow9_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-16) + z * ((-22) + z * ((-43) + z * ((-51) + z * ((-136) + z * (44 + z * ((-94) + z * ((-19) + z * (23 + z * ((-20) + z * ((-131) + z * ((-92) + z * ((-69) + z * ((-81) + z * ((-257) + z * ((-151) + z * ((-157) + z * ((-202) + z * ((-21) + z * ((-100) + z * (3 + z * ((-215) + z * ((-81) + z * (62 + z * ((-60) + z * (34 + z * ((-46) + z * ((-178) + z * ((-22) + z * ((-55) + z * (83 + z * (38 + z * ((-26) + z * (32 + z * (23 + z * (89 + z * (47 + z * 45))))))))))))))))))))))))))))))))))))))

theorem pow9_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z + (131 : R) * pow9_2_mul_t z := by
  simp only [u8, pow9_2_q, f, pow9_2, pow9_2_mul_t]
  simp only [pow8_131]
  ring

theorem pow9_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_2_mul_integer z


theorem pow9_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z * u8 z = pow9_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_2_mul z


theorem pow9_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 2 = pow9_2 z := by
  calc
    _ = u8 z ^ 1 * u8 z ^ 1 := by ring
    _ = u8 z * u8 z := by simp only [pow_one]
    _ = _ := pow9_2_root z hz


def pow9_4 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (17 + z * (24 + z * (86 + z * (74 + z * (62 + z * (80 + z * (24 + z * (34 + z * (24 + z * (120 + z * (88 + z * (125 + z * (130 + z * (100 + z * (66 + z * (54 + z * (99 + z * (117 + z * 88)))))))))))))))))))

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (122 + z * (89 + z * (78 + z * (107 + z * (35 + z * (111 + z * (25 + z * (44 + z * (10 + z * (5 + z * (42 + z * (5 + z * (15 + z * (42 + z * (72 + z * (59 + z * (89 + z * 41))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-13) + z * ((-22) + z * ((-73) + z * ((-53) + z * ((-84) + z * (8 + z * (28 + z * (24 + z * (48 + z * (207 + z * (122 + z * (253 + z * (238 + z * (399 + z * (325 + z * (478 + z * (419 + z * (510 + z * (377 + z * (546 + z * (481 + z * (533 + z * (526 + z * (551 + z * (493 + z * (458 + z * (355 + z * (402 + z * (265 + z * (254 + z * (250 + z * (178 + z * (63 + z * (97 + z * (28 + z * (14 + z * (23 + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow9_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z + (131 : R) * pow9_4_mul_t z := by
  simp only [pow9_2, pow9_4_q, f, pow9_4, pow9_4_mul_t]
  
  ring

theorem pow9_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_4_mul_integer z


theorem pow9_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_2 z * pow9_2 z = pow9_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_4_mul z


theorem pow9_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 4 = pow9_4 z := by
  calc
    _ = u8 z ^ 2 * u8 z ^ 2 := by ring
    _ = pow9_2 z * pow9_2 z := by rw [pow9_2_pow z hz]
    _ = _ := pow9_4_root z hz


def pow9_8 {R : Type*} [CommRing R] (z : R) : R := (75 + z * (74 + z * (9 + z * (76 + z * (68 + z * (123 + z * (121 + z * (23 + z * (52 + z * (7 + z * (120 + z * (102 + z * (7 + z * (83 + z * (34 + z * (121 + z * (22 + z * (56 + z * (103 + z * 57)))))))))))))))))))

def pow9_8_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (3 + z * (40 + z * (72 + z * (43 + z * (6 + z * (83 + z * (92 + z * (122 + z * (93 + z * (114 + z * (77 + z * (115 + z * (31 + z * (84 + z * (122 + z * (122 + z * (83 + z * 15))))))))))))))))))

def pow9_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * (3 + z * ((-7) + z * (37 + z * (16 + z * (19 + z * (81 + z * ((-3) + z * ((-43) + z * ((-2) + z * (3 + z * ((-113) + z * ((-60) + z * (31 + z * (21 + z * (11 + z * (105 + z * (97 + z * (152 + z * ((-12) + z * (53 + z * (125 + z * (238 + z * (242 + z * (258 + z * (199 + z * (155 + z * (182 + z * (247 + z * (390 + z * (396 + z * (374 + z * (271 + z * (132 + z * (102 + z * (144 + z * (188 + z * (149 + z * 59))))))))))))))))))))))))))))))))))))))

theorem pow9_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z + (131 : R) * pow9_8_mul_t z := by
  simp only [pow9_4, pow9_8_q, f, pow9_8, pow9_8_mul_t]
  
  ring

theorem pow9_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_8_mul_integer z


theorem pow9_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_4 z * pow9_4 z = pow9_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_8_mul z


theorem pow9_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 8 = pow9_8 z := by
  calc
    _ = u8 z ^ 4 * u8 z ^ 4 := by ring
    _ = pow9_4 z * pow9_4 z := by rw [pow9_4_pow z hz]
    _ = _ := pow9_8_root z hz


def pow9_16 {R : Type*} [CommRing R] (z : R) : R := (94 + z * (96 + z * (37 + z * (126 + z * (69 + z * (55 + z * (12 + z * (87 + z * (32 + z * (114 + z * (130 + z * (91 + z * (110 + z * (124 + z * (126 + z * (72 + z * (73 + z * (123 + z * (120 + z * 39)))))))))))))))))))

def pow9_16_q {R : Type*} [CommRing R] (z : R) : R := (108 + z * (19 + z * (74 + z * (9 + z * (122 + z * (74 + z * (31 + z * (87 + z * (115 + z * (13 + z * (102 + z * (76 + z * (121 + z * (5 + z * (73 + z * (87 + z * (8 + z * (96 + z * 105))))))))))))))))))

def pow9_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * (38 + z * ((-36) + z * (38 + z * (16 + z * (34 + z * (173 + z * (29 + z * (9 + z * ((-2) + z * (138 + z * (196 + z * ((-141) + z * ((-72) + z * (129 + z * (6 + z * (137 + z * ((-69) + z * (127 + z * ((-21) + z * (36 + z * (219 + z * ((-51) + z * (19 + z * (138 + z * (49 + z * ((-51) + z * ((-100) + z * (125 + z * (42 + z * (1 + z * ((-11) + z * (126 + z * (67 + z * (11 + z * (20 + z * (34 + z * (36 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow9_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z + (131 : R) * pow9_16_mul_t z := by
  simp only [pow9_8, pow9_16_q, f, pow9_16, pow9_16_mul_t]
  
  ring

theorem pow9_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_16_mul_integer z


theorem pow9_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_8 z * pow9_8 z = pow9_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_16_mul z


theorem pow9_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 16 = pow9_16 z := by
  calc
    _ = u8 z ^ 8 * u8 z ^ 8 := by ring
    _ = pow9_8 z * pow9_8 z := by rw [pow9_8_pow z hz]
    _ = _ := pow9_16_root z hz


def pow9_32 {R : Type*} [CommRing R] (z : R) : R := (47 + z * (71 + z * (94 + z * (107 + z * (67 + z * (93 + z * (58 + z * (31 + z * (18 + z * (75 + z * (129 + z * (75 + z * (64 + z * (55 + z * (84 + z * (46 + z * (20 + z * (119 + z * (15 + z * 29)))))))))))))))))))

def pow9_32_q {R : Type*} [CommRing R] (z : R) : R := (126 + z * (97 + z * (56 + z * (20 + z * (23 + z * (30 + z * (35 + z * (56 + z * (97 + z * (27 + z * (15 + z * (122 + z * (81 + z * (7 + z * (42 + z * (72 + z * (73 + z * (19 + z * 80))))))))))))))))))

def pow9_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (55 + z * (5 + z * (137 + z * (165 + z * (49 + z * (102 + z * (125 + z * (64 + z * (69 + z * (346 + z * (230 + z * (286 + z * (369 + z * (593 + z * (478 + z * (387 + z * (614 + z * (630 + z * (498 + z * (537 + z * (724 + z * (618 + z * (469 + z * (537 + z * (586 + z * (594 + z * (591 + z * (616 + z * (488 + z * (453 + z * (433 + z * (373 + z * (228 + z * (163 + z * (193 + z * (137 + z * (31 + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow9_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_16 z * pow9_16 z = pow9_32_q z * f z + pow9_32 z + (131 : R) * pow9_32_mul_t z := by
  simp only [pow9_16, pow9_32_q, f, pow9_32, pow9_32_mul_t]
  
  ring

theorem pow9_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_16 z * pow9_16 z = pow9_32_q z * f z + pow9_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_32_mul_integer z


theorem pow9_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_16 z * pow9_16 z = pow9_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_32_mul z


theorem pow9_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 32 = pow9_32 z := by
  calc
    _ = u8 z ^ 16 * u8 z ^ 16 := by ring
    _ = pow9_16 z * pow9_16 z := by rw [pow9_16_pow z hz]
    _ = _ := pow9_32_root z hz


def pow9_64 {R : Type*} [CommRing R] (z : R) : R := (45 + z * (10 + z * (101 + z * (111 + z * (121 + z * (86 + z * (104 + z * (28 + z * (100 + z * (21 + z * (123 + z * (89 + z * (66 + z * (43 + z * (59 + z * (107 + z * (22 + z * (58 + z * (34 + z * 43)))))))))))))))))))

def pow9_64_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (49 + z * (57 + z * (105 + z * (17 + z * (68 + z * (54 + z * (30 + z * (119 + z * (40 + z * (10 + z * (119 + z * (23 + z * (119 + z * (19 + z * (66 + z * (22 + z * (122 + z * 55))))))))))))))))))

def pow9_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (11 + z * (37 + z * (83 + z * (118 + z * (121 + z * (179 + z * (122 + z * (48 + z * (80 + z * (77 + z * (119 + z * (186 + z * (99 + z * (222 + z * (220 + z * (100 + z * (162 + z * (59 + z * (97 + z * (161 + z * (62 + z * (16 + z * (102 + z * ((-34) + z * ((-40) + z * ((-10) + z * (113 + z * (23 + z * ((-29) + z * ((-65) + z * (46 + z * ((-15) + z * ((-60) + z * (8 + z * ((-51) + z * ((-32) + z * ((-22) + z * 6))))))))))))))))))))))))))))))))))))))

theorem pow9_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_32 z * pow9_32 z = pow9_64_q z * f z + pow9_64 z + (131 : R) * pow9_64_mul_t z := by
  simp only [pow9_32, pow9_64_q, f, pow9_64, pow9_64_mul_t]
  
  ring

theorem pow9_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_32 z * pow9_32 z = pow9_64_q z * f z + pow9_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_64_mul_integer z


theorem pow9_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_32 z * pow9_32 z = pow9_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_64_mul z


theorem pow9_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 64 = pow9_64 z := by
  calc
    _ = u8 z ^ 32 * u8 z ^ 32 := by ring
    _ = pow9_32 z * pow9_32 z := by rw [pow9_32_pow z hz]
    _ = _ := pow9_64_root z hz


def pow9_65 {R : Type*} [CommRing R] (z : R) : R := (43 + z * (83 + z * (12 + z * (17 + z * (33 + z * (106 + z * (79 + z * (93 + z * (26 + z * (101 + z * (102 + z * (68 + z * (115 + z * (40 + z * (61 + z * (68 + z * (68 + z * (103 + z * (102 + z * 108)))))))))))))))))))

def pow9_65_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (93 + z * (85 + z * (65 + z * (16 + z * (128 + z * (4 + z * (0 + z * (26 + z * (67 + z * (105 + z * (27 + z * (73 + z * (39 + z * (75 + z * (29 + z * (26 + z * (118 + z * 36))))))))))))))))))

def pow9_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-56) + z * ((-49) + z * ((-48) + z * (46 + z * ((-45) + z * (81 + z * (88 + z * (182 + z * (123 + z * (170 + z * (179 + z * (196 + z * (21 + z * (124 + z * (252 + z * (181 + z * (184 + z * (111 + z * (226 + z * (246 + z * (105 + z * (181 + z * (278 + z * (161 + z * (89 + z * (37 + z * (160 + z * ((-21) + z * (52 + z * (21 + z * (67 + z * (74 + z * ((-10) + z * (43 + z * ((-14) + z * (5 + z * (19 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow9_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_64 z * u8 z = pow9_65_q z * f z + pow9_65 z + (131 : R) * pow9_65_mul_t z := by
  simp only [pow9_64, u8, pow9_65_q, f, pow9_65, pow9_65_mul_t]
  simp only [pow8_131]
  ring

theorem pow9_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_64 z * u8 z = pow9_65_q z * f z + pow9_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_65_mul_integer z


theorem pow9_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_64 z * u8 z = pow9_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_65_mul z


theorem pow9_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 65 = pow9_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow9_64_pow z hz]
  exact pow9_65_root z hz


def pow9_130 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (121 + z * (29 + z * (96 + z * (6 + z * (0 + z * (9 + z * (28 + z * (107 + z * (41 + z * (117 + z * (14 + z * (81 + z * (112 + z * (17 + z * (77 + z * (86 + z * (106 + z * (104 + z * 25)))))))))))))))))))

def pow9_130_q {R : Type*} [CommRing R] (z : R) : R := (74 + z * (21 + z * (46 + z * (94 + z * (40 + z * (77 + z * (35 + z * (115 + z * (75 + z * (46 + z * (0 + z * (44 + z * (84 + z * (12 + z * (10 + z * (50 + z * (22 + z * (87 + z * 5))))))))))))))))))

def pow9_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * (19 + z * ((-1) + z * ((-50) + z * ((-71) + z * ((-59) + z * (73 + z * ((-43) + z * ((-88) + z * ((-66) + z * (85 + z * (47 + z * (37 + z * (63 + z * (89 + z * (151 + z * (134 + z * (262 + z * (284 + z * (294 + z * (251 + z * (332 + z * (376 + z * (411 + z * (477 + z * (379 + z * (422 + z * (404 + z * (401 + z * (421 + z * (312 + z * (320 + z * (234 + z * (219 + z * (228 + z * (220 + z * (203 + z * (165 + z * 89))))))))))))))))))))))))))))))))))))))

theorem pow9_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_65 z * pow9_65 z = pow9_130_q z * f z + pow9_130 z + (131 : R) * pow9_130_mul_t z := by
  simp only [pow9_65, pow9_130_q, f, pow9_130, pow9_130_mul_t]
  
  ring

theorem pow9_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_65 z * pow9_65 z = pow9_130_q z * f z + pow9_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_130_mul_integer z


theorem pow9_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_65 z * pow9_65 z = pow9_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_130_mul z


theorem pow9_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 130 = pow9_130 z := by
  calc
    _ = u8 z ^ 65 * u8 z ^ 65 := by ring
    _ = pow9_65 z * pow9_65 z := by rw [pow9_65_pow z hz]
    _ = _ := pow9_130_root z hz


def pow9_131 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (64 + z * (40 + z * (56 + z * (61 + z * (111 + z * (123 + z * (71 + z * (85 + z * (4 + z * (43 + z * (1 + z * (123 + z * (38 + z * (24 + z * (53 + z * (18 + z * (3 + z * (129 + z * 43)))))))))))))))))))

def pow9_131_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (55 + z * (79 + z * (73 + z * (113 + z * (75 + z * (128 + z * (43 + z * (104 + z * (38 + z * (16 + z * (55 + z * (116 + z * (110 + z * (77 + z * (19 + z * (64 + z * (102 + z * 91))))))))))))))))))

def pow9_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * (21 + z * (55 + z * (39 + z * ((-8) + z * (54 + z * ((-38) + z * (4 + z * ((-34) + z * ((-46) + z * ((-39) + z * ((-209) + z * ((-16) + z * ((-179) + z * ((-23) + z * (48 + z * ((-133) + z * ((-31) + z * ((-8) + z * ((-55) + z * (62 + z * ((-79) + z * (49 + z * ((-76) + z * ((-42) + z * ((-1) + z * (0 + z * (122 + z * ((-23) + z * ((-17) + z * (50 + z * (41 + z * (75 + z * (10 + z * (43 + z * (63 + z * (32 + z * (25 + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow9_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_130 z * u8 z = pow9_131_q z * f z + pow9_131 z + (131 : R) * pow9_131_mul_t z := by
  simp only [pow9_130, u8, pow9_131_q, f, pow9_131, pow9_131_mul_t]
  simp only [pow8_131]
  ring

theorem pow9_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow9_130 z * u8 z = pow9_131_q z * f z + pow9_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow9_131_mul_integer z


theorem pow9_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow9_130 z * u8 z = pow9_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_131_mul z


theorem pow9_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u8 z ^ 131 = pow9_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow9_130_pow z hz]
  exact pow9_131_root z hz


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_131 z

theorem iterate9 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 9) = u9 z := by
  calc
    _ = (z ^ (131 ^ 8)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u8 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate8 z hz)
    _ = _ := pow9_131_pow z hz


def pow10_2 {R : Type*} [CommRing R] (z : R) : R := (89 + z * (7 + z * (14 + z * (38 + z * (98 + z * (61 + z * (43 + z * (42 + z * (52 + z * (99 + z * (82 + z * (100 + z * (4 + z * (129 + z * (122 + z * (76 + z * (94 + z * (50 + z * (20 + z * 104)))))))))))))))))))

def pow10_2_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (69 + z * (19 + z * (59 + z * (129 + z * (98 + z * (127 + z * (41 + z * (44 + z * (45 + z * (5 + z * (38 + z * (109 + z * (90 + z * (28 + z * (81 + z * (89 + z * (17 + z * 15))))))))))))))))))

def pow10_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-10) + z * ((-21) + z * (6 + z * ((-33) + z * ((-60) + z * (51 + z * (61 + z * ((-13) + z * ((-14) + z * (71 + z * ((-21) + z * (16 + z * ((-17) + z * ((-54) + z * ((-77) + z * ((-206) + z * ((-266) + z * (47 + z * ((-31) + z * ((-65) + z * ((-118) + z * ((-58) + z * ((-88) + z * (25 + z * ((-16) + z * (32 + z * ((-82) + z * ((-104) + z * ((-143) + z * (105 + z * ((-23) + z * ((-76) + z * (21 + z * ((-27) + z * ((-41) + z * (113 + z * (77 + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow10_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z + (131 : R) * pow10_2_mul_t z := by
  simp only [u9, pow10_2_q, f, pow10_2, pow10_2_mul_t]
  simp only [pow9_131]
  ring

theorem pow10_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_2_mul_integer z


theorem pow10_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z * u9 z = pow10_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_2_mul z


theorem pow10_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 2 = pow10_2 z := by
  calc
    _ = u9 z ^ 1 * u9 z ^ 1 := by ring
    _ = u9 z * u9 z := by simp only [pow_one]
    _ = _ := pow10_2_root z hz


def pow10_4 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (31 + z * (112 + z * (20 + z * (105 + z * (13 + z * (64 + z * (82 + z * (14 + z * (28 + z * (122 + z * (80 + z * (59 + z * (108 + z * (42 + z * (32 + z * (32 + z * (4 + z * (76 + z * 74)))))))))))))))))))

def pow10_4_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (117 + z * (115 + z * (66 + z * (96 + z * (3 + z * (123 + z * (73 + z * (31 + z * (81 + z * (66 + z * (81 + z * (63 + z * (92 + z * (53 + z * (128 + z * (115 + z * (62 + z * 74))))))))))))))))))

def pow10_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * ((-77) + z * ((-124) + z * ((-91) + z * ((-62) + z * ((-151) + z * ((-176) + z * ((-159) + z * ((-168) + z * ((-119) + z * ((-90) + z * ((-215) + z * ((-256) + z * ((-75) + z * ((-59) + z * ((-114) + z * ((-96) + z * ((-127) + z * ((-106) + z * (27 + z * ((-78) + z * ((-20) + z * (26 + z * (117 + z * (198 + z * (75 + z * (76 + z * (156 + z * (142 + z * (141 + z * (212 + z * ((-9) + z * (152 + z * (99 + z * ((-20) + z * (50 + z * (17 + z * ((-6) + z * 82))))))))))))))))))))))))))))))))))))))

theorem pow10_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z + (131 : R) * pow10_4_mul_t z := by
  simp only [pow10_2, pow10_4_q, f, pow10_4, pow10_4_mul_t]
  
  ring

theorem pow10_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_4_mul_integer z


theorem pow10_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_2 z * pow10_2 z = pow10_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_4_mul z


theorem pow10_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 4 = pow10_4 z := by
  calc
    _ = u9 z ^ 2 * u9 z ^ 2 := by ring
    _ = pow10_2 z * pow10_2 z := by rw [pow10_2_pow z hz]
    _ = _ := pow10_4_root z hz


def pow10_8 {R : Type*} [CommRing R] (z : R) : R := (97 + z * (93 + z * (10 + z * (98 + z * (56 + z * (4 + z * (57 + z * (3 + z * (109 + z * (4 + z * (25 + z * (73 + z * (85 + z * (61 + z * (81 + z * (7 + z * (2 + z * (88 + z * (25 + z * 66)))))))))))))))))))

def pow10_8_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (8 + z * (130 + z * (89 + z * (95 + z * (101 + z * (98 + z * (36 + z * (71 + z * (68 + z * (50 + z * (25 + z * (128 + z * (129 + z * (82 + z * (46 + z * (110 + z * (126 + z * 105))))))))))))))))))

def pow10_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-7) + z * ((-23) + z * ((-32) + z * ((-11) + z * ((-91) + z * ((-1) + z * ((-183) + z * ((-32) + z * ((-120) + z * ((-170) + z * ((-106) + z * ((-33) + z * ((-170) + z * ((-92) + z * ((-108) + z * ((-173) + z * ((-184) + z * ((-313) + z * ((-253) + z * ((-117) + z * ((-305) + z * ((-194) + z * ((-99) + z * ((-221) + z * ((-198) + z * ((-103) + z * ((-187) + z * ((-142) + z * ((-127) + z * ((-140) + z * ((-73) + z * ((-53) + z * ((-130) + z * ((-116) + z * ((-111) + z * ((-63) + z * (32 + z * 41))))))))))))))))))))))))))))))))))))))

theorem pow10_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z + (131 : R) * pow10_8_mul_t z := by
  simp only [pow10_4, pow10_8_q, f, pow10_8, pow10_8_mul_t]
  
  ring

theorem pow10_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_8_mul_integer z


theorem pow10_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_4 z * pow10_4 z = pow10_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_8_mul z


theorem pow10_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 8 = pow10_8 z := by
  calc
    _ = u9 z ^ 4 * u9 z ^ 4 := by ring
    _ = pow10_4 z * pow10_4 z := by rw [pow10_4_pow z hz]
    _ = _ := pow10_8_root z hz


def pow10_16 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (75 + z * (11 + z * (126 + z * (115 + z * (72 + z * (75 + z * (37 + z * (12 + z * (97 + z * (74 + z * (26 + z * (92 + z * (87 + z * (27 + z * (42 + z * (114 + z * (39 + z * (23 + z * 67)))))))))))))))))))

def pow10_16_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (31 + z * (18 + z * (90 + z * (87 + z * (58 + z * (25 + z * (95 + z * (120 + z * (117 + z * (85 + z * (71 + z * (49 + z * (83 + z * (50 + z * (37 + z * (39 + z * (74 + z * 33))))))))))))))))))

def pow10_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (102 + z * (31 + z * (91 + z * (107 + z * ((-74) + z * (45 + z * ((-19) + z * ((-90) + z * ((-58) + z * ((-186) + z * ((-81) + z * ((-104) + z * ((-176) + z * ((-8) + z * ((-182) + z * ((-261) + z * ((-136) + z * ((-184) + z * ((-233) + z * ((-120) + z * ((-287) + z * ((-185) + z * ((-163) + z * ((-244) + z * ((-50) + z * ((-207) + z * ((-90) + z * ((-129) + z * ((-87) + z * ((-9) + z * (78 + z * ((-25) + z * ((-28) + z * ((-19) + z * ((-30) + z * (41 + z * (8 + z * 33))))))))))))))))))))))))))))))))))))))

theorem pow10_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z + (131 : R) * pow10_16_mul_t z := by
  simp only [pow10_8, pow10_16_q, f, pow10_16, pow10_16_mul_t]
  
  ring

theorem pow10_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_16_mul_integer z


theorem pow10_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_8 z * pow10_8 z = pow10_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_16_mul z


theorem pow10_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 16 = pow10_16 z := by
  calc
    _ = u9 z ^ 8 * u9 z ^ 8 := by ring
    _ = pow10_8 z * pow10_8 z := by rw [pow10_8_pow z hz]
    _ = _ := pow10_16_root z hz


def pow10_32 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (71 + z * (91 + z * (87 + z * (12 + z * (113 + z * (98 + z * (9 + z * (16 + z * (2 + z * (37 + z * (82 + z * (57 + z * (7 + z * (130 + z * (86 + z * (96 + z * (22 + z * (11 + z * 15)))))))))))))))))))

def pow10_32_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (128 + z * (5 + z * (88 + z * (87 + z * (67 + z * (84 + z * (90 + z * (67 + z * (21 + z * (120 + z * (39 + z * (18 + z * (24 + z * (111 + z * (119 + z * (29 + z * (117 + z * 35))))))))))))))))))

def pow10_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * ((-55) + z * ((-16) + z * ((-86) + z * (47 + z * ((-35) + z * ((-4) + z * (142 + z * ((-25) + z * ((-20) + z * (44 + z * ((-83) + z * ((-130) + z * (110 + z * ((-34) + z * ((-56) + z * (67 + z * ((-15) + z * ((-72) + z * ((-28) + z * (67 + z * (0 + z * (10 + z * ((-50) + z * ((-32) + z * (28 + z * ((-104) + z * ((-88) + z * (61 + z * (46 + z * ((-66) + z * (39 + z * (62 + z * ((-97) + z * ((-46) + z * (49 + z * ((-31) + z * (5 + z * 34))))))))))))))))))))))))))))))))))))))

theorem pow10_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_16 z * pow10_16 z = pow10_32_q z * f z + pow10_32 z + (131 : R) * pow10_32_mul_t z := by
  simp only [pow10_16, pow10_32_q, f, pow10_32, pow10_32_mul_t]
  
  ring

theorem pow10_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_16 z * pow10_16 z = pow10_32_q z * f z + pow10_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_32_mul_integer z


theorem pow10_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_16 z * pow10_16 z = pow10_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_32_mul z


theorem pow10_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 32 = pow10_32 z := by
  calc
    _ = u9 z ^ 16 * u9 z ^ 16 := by ring
    _ = pow10_16 z * pow10_16 z := by rw [pow10_16_pow z hz]
    _ = _ := pow10_32_root z hz


def pow10_64 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (37 + z * (9 + z * (128 + z * (96 + z * (57 + z * (44 + z * (88 + z * (100 + z * (107 + z * (28 + z * (87 + z * (111 + z * (71 + z * (129 + z * (91 + z * (54 + z * (12 + z * (3 + z * 85)))))))))))))))))))

def pow10_64_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (4 + z * (43 + z * (48 + z * (123 + z * (8 + z * (92 + z * (59 + z * (8 + z * (8 + z * (78 + z * (19 + z * (97 + z * (100 + z * (95 + z * (5 + z * (6 + z * (21 + z * 94))))))))))))))))))

def pow10_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (15 + z * (53 + z * (88 + z * (155 + z * (33 + z * (111 + z * (186 + z * (93 + z * (60 + z * ((-47) + z * (20 + z * ((-22) + z * ((-25) + z * ((-44) + z * (23 + z * ((-43) + z * (246 + z * (212 + z * ((-45) + z * (3 + z * (70 + z * ((-4) + z * ((-100) + z * ((-259) + z * ((-96) + z * ((-130) + z * ((-24) + z * (37 + z * (75 + z * ((-55) + z * (49 + z * ((-7) + z * (12 + z * ((-17) + z * ((-36) + z * ((-22) + z * ((-47) + z * ((-45) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow10_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_32 z * pow10_32 z = pow10_64_q z * f z + pow10_64 z + (131 : R) * pow10_64_mul_t z := by
  simp only [pow10_32, pow10_64_q, f, pow10_64, pow10_64_mul_t]
  
  ring

theorem pow10_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_32 z * pow10_32 z = pow10_64_q z * f z + pow10_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_64_mul_integer z


theorem pow10_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_32 z * pow10_32 z = pow10_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_64_mul z


theorem pow10_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 64 = pow10_64 z := by
  calc
    _ = u9 z ^ 32 * u9 z ^ 32 := by ring
    _ = pow10_32 z * pow10_32 z := by rw [pow10_32_pow z hz]
    _ = _ := pow10_64_root z hz


def pow10_65 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (101 + z * (0 + z * (21 + z * (122 + z * (2 + z * (53 + z * (35 + z * (79 + z * (30 + z * (66 + z * (55 + z * (59 + z * (85 + z * (97 + z * (70 + z * (115 + z * (103 + z * (127 + z * 99)))))))))))))))))))

def pow10_65_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (24 + z * (8 + z * (28 + z * (117 + z * (48 + z * (67 + z * (113 + z * (82 + z * (59 + z * (85 + z * (50 + z * (25 + z * (60 + z * (63 + z * (20 + z * (10 + z * (31 + z * 118))))))))))))))))))

def pow10_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (12 + z * (9 + z * (55 + z * (62 + z * (49 + z * (59 + z * (91 + z * (95 + z * (123 + z * (149 + z * (88 + z * (48 + z * (155 + z * (138 + z * (146 + z * (163 + z * (138 + z * (55 + z * (162 + z * (120 + z * (193 + z * (49 + z * ((-48) + z * (104 + z * ((-18) + z * (12 + z * (136 + z * (28 + z * ((-33) + z * (9 + z * (76 + z * (102 + z * (53 + z * (14 + z * ((-22) + z * ((-60) + z * (25 + z * 27))))))))))))))))))))))))))))))))))))))

theorem pow10_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_64 z * u9 z = pow10_65_q z * f z + pow10_65 z + (131 : R) * pow10_65_mul_t z := by
  simp only [pow10_64, u9, pow10_65_q, f, pow10_65, pow10_65_mul_t]
  simp only [pow9_131]
  ring

theorem pow10_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_64 z * u9 z = pow10_65_q z * f z + pow10_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_65_mul_integer z


theorem pow10_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_64 z * u9 z = pow10_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_65_mul z


theorem pow10_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 65 = pow10_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow10_64_pow z hz]
  exact pow10_65_root z hz


def pow10_130 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (128 + z * (125 + z * (48 + z * (50 + z * (77 + z * (78 + z * (86 + z * (116 + z * (125 + z * (98 + z * (67 + z * (19 + z * (79 + z * (58 + z * (107 + z * (107 + z * (76 + z * (104 + z * 95)))))))))))))))))))

def pow10_130_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (29 + z * (107 + z * (3 + z * (99 + z * (128 + z * (122 + z * (8 + z * (120 + z * (31 + z * (68 + z * (31 + z * (63 + z * (94 + z * (12 + z * (1 + z * (77 + z * (6 + z * 107))))))))))))))))))

def pow10_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * (136 + z * ((-31) + z * ((-35) + z * (102 + z * ((-30) + z * ((-121) + z * ((-98) + z * (23 + z * ((-165) + z * ((-107) + z * ((-94) + z * ((-33) + z * ((-235) + z * (129 + z * (8 + z * (68 + z * (86 + z * (198 + z * (260 + z * (157 + z * ((-30) + z * (246 + z * (135 + z * (105 + z * (199 + z * (285 + z * (303 + z * (329 + z * (271 + z * (374 + z * (365 + z * (416 + z * (393 + z * (302 + z * (292 + z * (227 + z * (138 + z * 74))))))))))))))))))))))))))))))))))))))

theorem pow10_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_65 z * pow10_65 z = pow10_130_q z * f z + pow10_130 z + (131 : R) * pow10_130_mul_t z := by
  simp only [pow10_65, pow10_130_q, f, pow10_130, pow10_130_mul_t]
  
  ring

theorem pow10_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_65 z * pow10_65 z = pow10_130_q z * f z + pow10_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_130_mul_integer z


theorem pow10_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_65 z * pow10_65 z = pow10_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_130_mul z


theorem pow10_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 130 = pow10_130 z := by
  calc
    _ = u9 z ^ 65 * u9 z ^ 65 := by ring
    _ = pow10_65 z * pow10_65 z := by rw [pow10_65_pow z hz]
    _ = _ := pow10_130_root z hz


def pow10_131 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (7 + z * (120 + z * (55 + z * (19 + z * (59 + z * (37 + z * (77 + z * (0 + z * (130 + z * (127 + z * (41 + z * (111 + z * (126 + z * (13 + z * (111 + z * (36 + z * (116 + z * (125 + z * 1)))))))))))))))))))

def pow10_131_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (81 + z * (81 + z * (114 + z * (114 + z * (17 + z * (55 + z * (62 + z * (72 + z * (84 + z * (14 + z * (29 + z * (29 + z * (126 + z * (100 + z * (10 + z * (56 + z * (78 + z * 24))))))))))))))))))

def pow10_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (12 + z * (40 + z * (66 + z * (21 + z * (13 + z * (48 + z * (84 + z * (179 + z * (134 + z * (133 + z * (161 + z * (104 + z * (105 + z * (169 + z * (153 + z * (129 + z * (167 + z * (105 + z * (64 + z * (200 + z * (219 + z * (169 + z * (144 + z * (304 + z * (159 + z * (68 + z * (104 + z * (154 + z * (119 + z * (39 + z * (26 + z * (127 + z * (5 + z * (62 + z * (119 + z * (53 + z * (79 + z * (115 + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow10_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_130 z * u9 z = pow10_131_q z * f z + pow10_131 z + (131 : R) * pow10_131_mul_t z := by
  simp only [pow10_130, u9, pow10_131_q, f, pow10_131, pow10_131_mul_t]
  simp only [pow9_131]
  ring

theorem pow10_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow10_130 z * u9 z = pow10_131_q z * f z + pow10_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow10_131_mul_integer z


theorem pow10_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow10_130 z * u9 z = pow10_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_131_mul z


theorem pow10_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u9 z ^ 131 = pow10_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow10_130_pow z hz]
  exact pow10_131_root z hz


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_131 z

theorem iterate10 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 10) = u10 z := by
  calc
    _ = (z ^ (131 ^ 9)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u9 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate9 z hz)
    _ = _ := pow10_131_pow z hz

end DimensionTen.Mod131

end

end OAI
