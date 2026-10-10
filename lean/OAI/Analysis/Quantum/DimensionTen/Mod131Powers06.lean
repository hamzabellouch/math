import OAI.Analysis.Quantum.DimensionTen.Mod131Powers05

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow11_2 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (50 + z * (62 + z * (14 + z * (102 + z * (58 + z * (95 + z * (51 + z * (111 + z * (81 + z * (25 + z * (59 + z * (41 + z * (128 + z * (55 + z * (121 + z * (53 + z * (15 + z * (61 + z * 66)))))))))))))))))))

def pow11_2_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (37 + z * (38 + z * (79 + z * (13 + z * (78 + z * (87 + z * (105 + z * (1 + z * (26 + z * (93 + z * (37 + z * (95 + z * (121 + z * (75 + z * (96 + z * (117 + z * (53 + z * 1))))))))))))))))))

def pow11_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-40) + z * ((-12) + z * ((-38) + z * (22 + z * ((-40) + z * ((-55) + z * ((-68) + z * ((-124) + z * (35 + z * ((-102) + z * ((-27) + z * (110 + z * ((-26) + z * ((-19) + z * (98 + z * ((-29) + z * (21 + z * ((-50) + z * (216 + z * (288 + z * (1 + z * (281 + z * (68 + z * (138 + z * (216 + z * (131 + z * (386 + z * (244 + z * (59 + z * (315 + z * (96 + z * (10 + z * (115 + z * (51 + z * (138 + z * (93 + z * (1 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z + (131 : R) * pow11_2_mul_t z := by
  simp only [u10, pow11_2_q, f, pow11_2, pow11_2_mul_t]
  simp only [pow10_131]
  ring

theorem pow11_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_2_mul_integer z


theorem pow11_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z * u10 z = pow11_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_2_mul z


theorem pow11_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 2 = pow11_2 z := by
  calc
    _ = u10 z ^ 1 * u10 z ^ 1 := by ring
    _ = u10 z * u10 z := by simp only [pow_one]
    _ = _ := pow11_2_root z hz


def pow11_4 {R : Type*} [CommRing R] (z : R) : R := (42 + z * (92 + z * (74 + z * (47 + z * (7 + z * (34 + z * (45 + z * (105 + z * (45 + z * (113 + z * (31 + z * (129 + z * (61 + z * (95 + z * (109 + z * (89 + z * (13 + z * (81 + z * (116 + z * 14)))))))))))))))))))

def pow11_4_q {R : Type*} [CommRing R] (z : R) : R := (106 + z * (128 + z * (106 + z * (11 + z * (107 + z * (86 + z * (116 + z * (106 + z * (33 + z * (19 + z * (78 + z * (24 + z * (0 + z * (49 + z * (104 + z * (114 + z * (31 + z * (110 + z * 33))))))))))))))))))

def pow11_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-54) + z * ((-78) + z * ((-67) + z * ((-68) + z * ((-127) + z * ((-94) + z * ((-117) + z * ((-46) + z * ((-132) + z * (4 + z * ((-110) + z * ((-90) + z * ((-21) + z * (2 + z * (26 + z * (25 + z * (41 + z * ((-140) + z * (66 + z * (110 + z * (169 + z * (35 + z * (118 + z * (179 + z * (2 + z * (56 + z * (160 + z * (149 + z * (58 + z * (64 + z * (101 + z * (62 + z * ((-17) + z * (38 + z * ((-11) + z * ((-27) + z * (44 + z * 33))))))))))))))))))))))))))))))))))))))

theorem pow11_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z + (131 : R) * pow11_4_mul_t z := by
  simp only [pow11_2, pow11_4_q, f, pow11_4, pow11_4_mul_t]
  
  ring

theorem pow11_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_4_mul_integer z


theorem pow11_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_2 z * pow11_2 z = pow11_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_4_mul z


theorem pow11_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 4 = pow11_4 z := by
  calc
    _ = u10 z ^ 2 * u10 z ^ 2 := by ring
    _ = pow11_2 z * pow11_2 z := by rw [pow11_2_pow z hz]
    _ = _ := pow11_4_root z hz


def pow11_8 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (100 + z * (45 + z * (55 + z * (82 + z * (117 + z * (28 + z * (55 + z * (67 + z * (44 + z * (25 + z * (0 + z * (47 + z * (102 + z * (127 + z * (43 + z * (36 + z * (117 + z * (22 + z * 41)))))))))))))))))))

def pow11_8_q {R : Type*} [CommRing R] (z : R) : R := (47 + z * (111 + z * (102 + z * (12 + z * (12 + z * (49 + z * (97 + z * (75 + z * (107 + z * (97 + z * (30 + z * (98 + z * (26 + z * (35 + z * (7 + z * (111 + z * (96 + z * (6 + z * 65))))))))))))))))))

def pow11_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-1) + z * (10 + z * (30 + z * (8 + z * ((-64) + z * ((-114) + z * ((-38) + z * (14 + z * ((-35) + z * ((-25) + z * ((-33) + z * (27 + z * ((-87) + z * (113 + z * (135 + z * (127 + z * ((-18) + z * (146 + z * (94 + z * (158 + z * (150 + z * (202 + z * (99 + z * (221 + z * (281 + z * (234 + z * (143 + z * (202 + z * (259 + z * (174 + z * (163 + z * (194 + z * (85 + z * ((-52) + z * (70 + z * (87 + z * ((-8) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow11_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z + (131 : R) * pow11_8_mul_t z := by
  simp only [pow11_4, pow11_8_q, f, pow11_8, pow11_8_mul_t]
  
  ring

theorem pow11_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_8_mul_integer z


theorem pow11_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_4 z * pow11_4 z = pow11_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_8_mul z


theorem pow11_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 8 = pow11_8 z := by
  calc
    _ = u10 z ^ 4 * u10 z ^ 4 := by ring
    _ = pow11_4 z * pow11_4 z := by rw [pow11_4_pow z hz]
    _ = _ := pow11_8_root z hz


def pow11_16 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (51 + z * (31 + z * (69 + z * (91 + z * (86 + z * (13 + z * (67 + z * (11 + z * (32 + z * (76 + z * (25 + z * (103 + z * (57 + z * (27 + z * (68 + z * (98 + z * (8 + z * (63 + z * 88)))))))))))))))))))

def pow11_16_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (16 + z * (104 + z * (118 + z * (43 + z * (99 + z * (76 + z * (91 + z * (122 + z * (98 + z * (104 + z * (29 + z * (26 + z * (85 + z * (69 + z * (54 + z * (54 + z * (112 + z * 109))))))))))))))))))

def pow11_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * (54 + z * (17 + z * (14 + z * (5 + z * (39 + z * (109 + z * ((-90) + z * ((-42) + z * (5 + z * ((-119) + z * ((-260) + z * ((-187) + z * ((-162) + z * ((-76) + z * ((-122) + z * ((-183) + z * ((-20) + z * ((-71) + z * ((-134) + z * ((-130) + z * ((-166) + z * ((-88) + z * ((-165) + z * ((-163) + z * ((-256) + z * ((-175) + z * ((-29) + z * ((-81) + z * ((-116) + z * (23 + z * (116 + z * (26 + z * ((-26) + z * ((-22) + z * ((-57) + z * ((-29) + z * ((-42) + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow11_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z + (131 : R) * pow11_16_mul_t z := by
  simp only [pow11_8, pow11_16_q, f, pow11_16, pow11_16_mul_t]
  
  ring

theorem pow11_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_16_mul_integer z


theorem pow11_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_8 z * pow11_8 z = pow11_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_16_mul z


theorem pow11_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 16 = pow11_16 z := by
  calc
    _ = u10 z ^ 8 * u10 z ^ 8 := by ring
    _ = pow11_8 z * pow11_8 z := by rw [pow11_8_pow z hz]
    _ = _ := pow11_16_root z hz


def pow11_32 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (83 + z * (34 + z * (122 + z * (113 + z * (7 + z * (61 + z * (44 + z * (112 + z * (59 + z * (103 + z * (125 + z * (66 + z * (31 + z * (10 + z * (117 + z * (30 + z * (79 + z * (58 + z * 114)))))))))))))))))))

def pow11_32_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (8 + z * (12 + z * (41 + z * (9 + z * (108 + z * (65 + z * (50 + z * (56 + z * (93 + z * (42 + z * (78 + z * (30 + z * (15 + z * (39 + z * (55 + z * (98 + z * (11 + z * 15))))))))))))))))))

def pow11_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (33 + z * (43 + z * (27 + z * (78 + z * (123 + z * (98 + z * (73 + z * (75 + z * (52 + z * (22 + z * (15 + z * ((-45) + z * (50 + z * ((-17) + z * (11 + z * (101 + z * (28 + z * (55 + z * ((-34) + z * (169 + z * (77 + z * ((-22) + z * (72 + z * (78 + z * ((-35) + z * (30 + z * (63 + z * ((-77) + z * (109 + z * (82 + z * (94 + z * (188 + z * (70 + z * (21 + z * (100 + z * (79 + z * (28 + z * (77 + z * 59))))))))))))))))))))))))))))))))))))))

theorem pow11_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_16 z * pow11_16 z = pow11_32_q z * f z + pow11_32 z + (131 : R) * pow11_32_mul_t z := by
  simp only [pow11_16, pow11_32_q, f, pow11_32, pow11_32_mul_t]
  
  ring

theorem pow11_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_16 z * pow11_16 z = pow11_32_q z * f z + pow11_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_32_mul_integer z


theorem pow11_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_16 z * pow11_16 z = pow11_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_32_mul z


theorem pow11_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 32 = pow11_32 z := by
  calc
    _ = u10 z ^ 16 * u10 z ^ 16 := by ring
    _ = pow11_16 z * pow11_16 z := by rw [pow11_16_pow z hz]
    _ = _ := pow11_32_root z hz


def pow11_64 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (125 + z * (130 + z * (60 + z * (128 + z * (105 + z * (73 + z * (51 + z * (84 + z * (4 + z * (104 + z * (72 + z * (40 + z * (116 + z * (35 + z * (61 + z * (53 + z * (46 + z * (66 + z * 105)))))))))))))))))))

def pow11_64_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (98 + z * (130 + z * (25 + z * (122 + z * (41 + z * (63 + z * (90 + z * (98 + z * (77 + z * (7 + z * (83 + z * (100 + z * (106 + z * (59 + z * (17 + z * (45 + z * (45 + z * 27))))))))))))))))))

def pow11_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (32 + z * ((-17) + z * (55 + z * (120 + z * (33 + z * ((-17) + z * (89 + z * (32 + z * ((-58) + z * (100 + z * (201 + z * (144 + z * ((-40) + z * (128 + z * (108 + z * (52 + z * ((-39) + z * (192 + z * (289 + z * (96 + z * (212 + z * (251 + z * (240 + z * ((-67) + z * (126 + z * (222 + z * (273 + z * (176 + z * (156 + z * (206 + z * (45 + z * (80 + z * (65 + z * (214 + z * (69 + z * (128 + z * (87 + z * 99))))))))))))))))))))))))))))))))))))))

theorem pow11_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_32 z * pow11_32 z = pow11_64_q z * f z + pow11_64 z + (131 : R) * pow11_64_mul_t z := by
  simp only [pow11_32, pow11_64_q, f, pow11_64, pow11_64_mul_t]
  
  ring

theorem pow11_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_32 z * pow11_32 z = pow11_64_q z * f z + pow11_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_64_mul_integer z


theorem pow11_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_32 z * pow11_32 z = pow11_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_64_mul z


theorem pow11_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 64 = pow11_64 z := by
  calc
    _ = u10 z ^ 32 * u10 z ^ 32 := by ring
    _ = pow11_32 z * pow11_32 z := by rw [pow11_32_pow z hz]
    _ = _ := pow11_64_root z hz


def pow11_65 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (42 + z * (81 + z * (123 + z * (74 + z * (7 + z * (119 + z * (79 + z * (87 + z * (40 + z * (55 + z * (96 + z * (115 + z * (66 + z * (109 + z * (28 + z * (3 + z * (72 + z * (13 + z * 12)))))))))))))))))))

def pow11_65_q {R : Type*} [CommRing R] (z : R) : R := (75 + z * (27 + z * (105 + z * (35 + z * (36 + z * (65 + z * (32 + z * (84 + z * (33 + z * (90 + z * (106 + z * (54 + z * (77 + z * (54 + z * (30 + z * (88 + z * (81 + z * (104 + z * 105))))))))))))))))))

def pow11_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-8) + z * ((-35) + z * (64 + z * (83 + z * (13 + z * (103 + z * (45 + z * (95 + z * ((-2) + z * (94 + z * (119 + z * (95 + z * (169 + z * (196 + z * (214 + z * (157 + z * (200 + z * (87 + z * (246 + z * (219 + z * (133 + z * (155 + z * (144 + z * (59 + z * (102 + z * (54 + z * (13 + z * (171 + z * (21 + z * (80 + z * (138 + z * (87 + z * (1 + z * (10 + z * (4 + z * (56 + z * (47 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_64 z * u10 z = pow11_65_q z * f z + pow11_65 z + (131 : R) * pow11_65_mul_t z := by
  simp only [pow11_64, u10, pow11_65_q, f, pow11_65, pow11_65_mul_t]
  simp only [pow10_131]
  ring

theorem pow11_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_64 z * u10 z = pow11_65_q z * f z + pow11_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_65_mul_integer z


theorem pow11_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_64 z * u10 z = pow11_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_65_mul z


theorem pow11_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 65 = pow11_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow11_64_pow z hz]
  exact pow11_65_root z hz


def pow11_130 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (42 + z * (14 + z * (87 + z * (128 + z * (116 + z * (35 + z * (36 + z * (45 + z * (78 + z * (49 + z * (112 + z * (109 + z * (11 + z * (111 + z * (110 + z * (110 + z * (117 + z * (55 + z * 106)))))))))))))))))))

def pow11_130_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (85 + z * (60 + z * (35 + z * (68 + z * (94 + z * (108 + z * (38 + z * (34 + z * (71 + z * (121 + z * (45 + z * (86 + z * (126 + z * (12 + z * (4 + z * (93 + z * (109 + z * 13))))))))))))))))))

def pow11_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-16) + z * ((-34) + z * ((-29) + z * (29 + z * (49 + z * (11 + z * (53 + z * (47 + z * (39 + z * (94 + z * (101 + z * (26 + z * (64 + z * (29 + z * (193 + z * (215 + z * (159 + z * (3 + z * (18 + z * (84 + z * (163 + z * ((-84) + z * ((-69) + z * (58 + z * ((-64) + z * ((-6) + z * (33 + z * ((-19) + z * ((-113) + z * ((-132) + z * ((-72) + z * (8 + z * ((-99) + z * ((-90) + z * ((-48) + z * ((-86) + z * ((-47) + z * ((-5) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow11_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_65 z * pow11_65 z = pow11_130_q z * f z + pow11_130 z + (131 : R) * pow11_130_mul_t z := by
  simp only [pow11_65, pow11_130_q, f, pow11_130, pow11_130_mul_t]
  
  ring

theorem pow11_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_65 z * pow11_65 z = pow11_130_q z * f z + pow11_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_130_mul_integer z


theorem pow11_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_65 z * pow11_65 z = pow11_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_130_mul z


theorem pow11_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 130 = pow11_130 z := by
  calc
    _ = u10 z ^ 65 * u10 z ^ 65 := by ring
    _ = pow11_65 z * pow11_65 z := by rw [pow11_65_pow z hz]
    _ = _ := pow11_130_root z hz


def pow11_131 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (44 + z * (41 + z * (40 + z * (103 + z * (20 + z * (46 + z * (45 + z * (62 + z * (28 + z * (70 + z * (16 + z * (104 + z * (109 + z * (66 + z * (65 + z * (29 + z * (49 + z * (116 + z * 122)))))))))))))))))))

def pow11_131_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (18 + z * (117 + z * (11 + z * (42 + z * (35 + z * (92 + z * (3 + z * (89 + z * (28 + z * (17 + z * (42 + z * (128 + z * (66 + z * (62 + z * (98 + z * (120 + z * (21 + z * 106))))))))))))))))))

def pow11_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-4) + z * ((-37) + z * (9 + z * ((-25) + z * (52 + z * (45 + z * (35 + z * (33 + z * ((-5) + z * (31 + z * (75 + z * (110 + z * (55 + z * (228 + z * (105 + z * (189 + z * (146 + z * (247 + z * (205 + z * (140 + z * (394 + z * (349 + z * (117 + z * (255 + z * (161 + z * (302 + z * (261 + z * (279 + z * (317 + z * (182 + z * (108 + z * (251 + z * (128 + z * (133 + z * (80 + z * (88 + z * (48 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_130 z * u10 z = pow11_131_q z * f z + pow11_131 z + (131 : R) * pow11_131_mul_t z := by
  simp only [pow11_130, u10, pow11_131_q, f, pow11_131, pow11_131_mul_t]
  simp only [pow10_131]
  ring

theorem pow11_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow11_130 z * u10 z = pow11_131_q z * f z + pow11_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow11_131_mul_integer z


theorem pow11_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow11_130 z * u10 z = pow11_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_131_mul z


theorem pow11_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u10 z ^ 131 = pow11_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow11_130_pow z hz]
  exact pow11_131_root z hz


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_131 z

theorem iterate11 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 11) = u11 z := by
  calc
    _ = (z ^ (131 ^ 10)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u10 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate10 z hz)
    _ = _ := pow11_131_pow z hz


def pow12_2 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (101 + z * (111 + z * (87 + z * (32 + z * (15 + z * (72 + z * (0 + z * (1 + z * (97 + z * (0 + z * (50 + z * (40 + z * (25 + z * (24 + z * (70 + z * (126 + z * (70 + z * (7 + z * 53)))))))))))))))))))

def pow12_2_q {R : Type*} [CommRing R] (z : R) : R := (41 + z * (1 + z * (96 + z * (95 + z * (130 + z * (36 + z * (34 + z * (87 + z * (50 + z * (54 + z * (118 + z * (51 + z * (25 + z * (118 + z * (78 + z * (91 + z * (115 + z * (33 + z * 81))))))))))))))))))

def pow12_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (66 + z * (54 + z * (22 + z * (12 + z * (50 + z * ((-34) + z * (3 + z * ((-65) + z * ((-9) + z * ((-117) + z * ((-14) + z * ((-180) + z * ((-32) + z * ((-5) + z * ((-28) + z * ((-225) + z * ((-44) + z * ((-46) + z * ((-74) + z * (64 + z * ((-101) + z * ((-140) + z * (1 + z * ((-30) + z * ((-39) + z * (48 + z * ((-14) + z * (52 + z * (54 + z * ((-7) + z * (120 + z * (228 + z * (157 + z * (91 + z * (27 + z * (37 + z * (140 + z * (175 + z * 113))))))))))))))))))))))))))))))))))))))

theorem pow12_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z + (131 : R) * pow12_2_mul_t z := by
  simp only [u11, pow12_2_q, f, pow12_2, pow12_2_mul_t]
  simp only [pow11_131]
  ring

theorem pow12_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_2_mul_integer z


theorem pow12_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z * u11 z = pow12_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_2_mul z


theorem pow12_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 2 = pow12_2 z := by
  calc
    _ = u11 z ^ 1 * u11 z ^ 1 := by ring
    _ = u11 z * u11 z := by simp only [pow_one]
    _ = _ := pow12_2_root z hz


def pow12_4 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (70 + z * (51 + z * (89 + z * (36 + z * (83 + z * (22 + z * (54 + z * (84 + z * (26 + z * (73 + z * (1 + z * (129 + z * (81 + z * (84 + z * (28 + z * (124 + z * (20 + z * (97 + z * 125)))))))))))))))))))

def pow12_4_q {R : Type*} [CommRing R] (z : R) : R := (106 + z * (127 + z * (17 + z * (92 + z * (93 + z * (19 + z * (37 + z * (43 + z * (109 + z * (63 + z * (123 + z * (83 + z * (44 + z * (103 + z * (61 + z * (37 + z * (88 + z * (58 + z * 58))))))))))))))))))

def pow12_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (69 + z * (98 + z * (177 + z * (208 + z * (130 + z * ((-26) + z * (63 + z * (0 + z * ((-207) + z * ((-51) + z * ((-109) + z * ((-145) + z * ((-199) + z * ((-252) + z * ((-224) + z * ((-153) + z * ((-127) + z * ((-24) + z * ((-45) + z * ((-175) + z * ((-220) + z * ((-285) + z * ((-241) + z * ((-291) + z * ((-273) + z * ((-143) + z * ((-237) + z * ((-212) + z * ((-78) + z * ((-222) + z * ((-73) + z * (17 + z * (48 + z * (26 + z * ((-11) + z * (17 + z * (1 + z * ((-24) + z * 21))))))))))))))))))))))))))))))))))))))

theorem pow12_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z + (131 : R) * pow12_4_mul_t z := by
  simp only [pow12_2, pow12_4_q, f, pow12_4, pow12_4_mul_t]
  
  ring

theorem pow12_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_4_mul_integer z


theorem pow12_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_2 z * pow12_2 z = pow12_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_4_mul z


theorem pow12_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 4 = pow12_4 z := by
  calc
    _ = u11 z ^ 2 * u11 z ^ 2 := by ring
    _ = pow12_2 z * pow12_2 z := by rw [pow12_2_pow z hz]
    _ = _ := pow12_4_root z hz


def pow12_8 {R : Type*} [CommRing R] (z : R) : R := (41 + z * (53 + z * (5 + z * (55 + z * (58 + z * (57 + z * (35 + z * (9 + z * (40 + z * (84 + z * (92 + z * (107 + z * (74 + z * (48 + z * (24 + z * (110 + z * (24 + z * (63 + z * (40 + z * 57)))))))))))))))))))

def pow12_8_q {R : Type*} [CommRing R] (z : R) : R := (126 + z * (12 + z * (0 + z * (110 + z * (66 + z * (84 + z * (35 + z * (13 + z * (31 + z * (25 + z * (34 + z * (84 + z * (48 + z * (62 + z * (65 + z * (0 + z * (38 + z * (128 + z * 36))))))))))))))))))

def pow12_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (15 + z * (19 + z * (67 + z * (13 + z * ((-41) + z * (90 + z * ((-10) + z * ((-7) + z * (32 + z * (86 + z * ((-63) + z * (0 + z * (117 + z * (76 + z * (169 + z * (21 + z * (201 + z * (105 + z * (222 + z * (304 + z * (206 + z * (128 + z * (153 + z * (265 + z * (64 + z * (347 + z * (167 + z * (236 + z * (100 + z * (152 + z * (329 + z * (281 + z * (98 + z * (151 + z * (176 + z * (29 + z * (166 + z * 119))))))))))))))))))))))))))))))))))))))

theorem pow12_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z + (131 : R) * pow12_8_mul_t z := by
  simp only [pow12_4, pow12_8_q, f, pow12_8, pow12_8_mul_t]
  
  ring

theorem pow12_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_8_mul_integer z


theorem pow12_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_4 z * pow12_4 z = pow12_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_8_mul z


theorem pow12_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 8 = pow12_8 z := by
  calc
    _ = u11 z ^ 4 * u11 z ^ 4 := by ring
    _ = pow12_4 z * pow12_4 z := by rw [pow12_4_pow z hz]
    _ = _ := pow12_8_root z hz


def pow12_16 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (74 + z * (65 + z * (108 + z * (47 + z * (106 + z * (69 + z * (73 + z * (87 + z * (103 + z * (20 + z * (11 + z * (23 + z * (39 + z * (73 + z * (96 + z * (102 + z * (121 + z * (14 + z * 64)))))))))))))))))))

def pow12_16_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (105 + z * (3 + z * (88 + z * (99 + z * (23 + z * (20 + z * (4 + z * (87 + z * (117 + z * (47 + z * (76 + z * (63 + z * (116 + z * (46 + z * (12 + z * (104 + z * (119 + z * 105))))))))))))))))))

def pow12_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-15) + z * ((-25) + z * ((-52) + z * ((-20) + z * ((-77) + z * ((-78) + z * ((-14) + z * ((-143) + z * ((-107) + z * ((-39) + z * ((-72) + z * ((-114) + z * ((-126) + z * ((-89) + z * ((-13) + z * ((-124) + z * ((-225) + z * ((-112) + z * ((-96) + z * ((-124) + z * ((-140) + z * ((-109) + z * ((-18) + z * ((-70) + z * ((-130) + z * ((-21) + z * ((-18) + z * ((-35) + z * ((-129) + z * ((-2) + z * ((-50) + z * ((-25) + z * ((-65) + z * ((-26) + z * ((-86) + z * ((-41) + z * ((-19) + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow12_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z + (131 : R) * pow12_16_mul_t z := by
  simp only [pow12_8, pow12_16_q, f, pow12_16, pow12_16_mul_t]
  
  ring

theorem pow12_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_16_mul_integer z


theorem pow12_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_8 z * pow12_8 z = pow12_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_16_mul z


theorem pow12_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 16 = pow12_16 z := by
  calc
    _ = u11 z ^ 8 * u11 z ^ 8 := by ring
    _ = pow12_8 z * pow12_8 z := by rw [pow12_8_pow z hz]
    _ = _ := pow12_16_root z hz


def pow12_32 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (33 + z * (27 + z * (63 + z * (89 + z * (122 + z * (55 + z * (39 + z * (76 + z * (10 + z * (37 + z * (56 + z * (110 + z * (79 + z * (105 + z * (3 + z * (56 + z * (52 + z * (76 + z * 1)))))))))))))))))))

def pow12_32_q {R : Type*} [CommRing R] (z : R) : R := (53 + z * (130 + z * (74 + z * (21 + z * (113 + z * (113 + z * (19 + z * (41 + z * (15 + z * (127 + z * (92 + z * (13 + z * (69 + z * (29 + z * (48 + z * (100 + z * (123 + z * (6 + z * 35))))))))))))))))))

def pow12_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (67 + z * (52 + z * (47 + z * (142 + z * (92 + z * (109 + z * (107 + z * (176 + z * (244 + z * (131 + z * (157 + z * (136 + z * ((-1) + z * ((-43) + z * (48 + z * (150 + z * (118 + z * (143 + z * (153 + z * (258 + z * (67 + z * (72 + z * (280 + z * (95 + z * (217 + z * (126 + z * (40 + z * ((-108) + z * ((-56) + z * (8 + z * (130 + z * (128 + z * (152 + z * (151 + z * (96 + z * (47 + z * (100 + z * ((-4) + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow12_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_16 z * pow12_16 z = pow12_32_q z * f z + pow12_32 z + (131 : R) * pow12_32_mul_t z := by
  simp only [pow12_16, pow12_32_q, f, pow12_32, pow12_32_mul_t]
  
  ring

theorem pow12_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_16 z * pow12_16 z = pow12_32_q z * f z + pow12_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_32_mul_integer z


theorem pow12_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_16 z * pow12_16 z = pow12_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_32_mul z


theorem pow12_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 32 = pow12_32 z := by
  calc
    _ = u11 z ^ 16 * u11 z ^ 16 := by ring
    _ = pow12_16 z * pow12_16 z := by rw [pow12_16_pow z hz]
    _ = _ := pow12_32_root z hz


def pow12_64 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (63 + z * (79 + z * (24 + z * (82 + z * (84 + z * (14 + z * (89 + z * (78 + z * (98 + z * (78 + z * (48 + z * (121 + z * (70 + z * (124 + z * (122 + z * (37 + z * (59 + z * (46 + z * 27)))))))))))))))))))

def pow12_64_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (26 + z * (87 + z * (105 + z * (84 + z * (5 + z * (2 + z * (31 + z * (12 + z * (115 + z * (34 + z * (81 + z * (59 + z * (66 + z * (68 + z * (4 + z * (14 + z * (86 + z * 1))))))))))))))))))

def pow12_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-23) + z * ((-58) + z * ((-61) + z * ((-86) + z * ((-59) + z * (14 + z * ((-22) + z * (25 + z * (41 + z * (60 + z * ((-73) + z * ((-21) + z * ((-23) + z * ((-93) + z * (1 + z * (60 + z * (159 + z * (122 + z * (84 + z * (23 + z * (33 + z * (40 + z * (128 + z * (112 + z * (20 + z * (118 + z * (11 + z * (17 + z * (21 + z * (91 + z * (82 + z * (50 + z * ((-49) + z * (44 + z * (15 + z * (1 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow12_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_32 z * pow12_32 z = pow12_64_q z * f z + pow12_64 z + (131 : R) * pow12_64_mul_t z := by
  simp only [pow12_32, pow12_64_q, f, pow12_64, pow12_64_mul_t]
  
  ring

theorem pow12_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_32 z * pow12_32 z = pow12_64_q z * f z + pow12_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_64_mul_integer z


theorem pow12_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_32 z * pow12_32 z = pow12_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_64_mul z


theorem pow12_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 64 = pow12_64 z := by
  calc
    _ = u11 z ^ 32 * u11 z ^ 32 := by ring
    _ = pow12_32 z * pow12_32 z := by rw [pow12_32_pow z hz]
    _ = _ := pow12_64_root z hz


def pow12_65 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (104 + z * (1 + z * (36 + z * (66 + z * (129 + z * (54 + z * (35 + z * (10 + z * (21 + z * (6 + z * (107 + z * (23 + z * (110 + z * (91 + z * (5 + z * (69 + z * (14 + z * (127 + z * 73)))))))))))))))))))

def pow12_65_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (5 + z * (71 + z * (41 + z * (115 + z * (45 + z * (89 + z * (128 + z * (42 + z * (57 + z * (106 + z * (13 + z * (100 + z * (113 + z * (101 + z * (79 + z * (83 + z * (23 + z * 19))))))))))))))))))

def pow12_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (40 + z * (58 + z * (60 + z * (36 + z * (57 + z * (63 + z * (10 + z * ((-22) + z * (31 + z * ((-1) + z * (18 + z * ((-59) + z * (18 + z * (51 + z * (33 + z * ((-24) + z * (50 + z * ((-1) + z * ((-4) + z * (107 + z * (38 + z * (6 + z * (98 + z * (17 + z * (69 + z * (23 + z * (105 + z * (228 + z * (163 + z * (112 + z * (160 + z * (129 + z * (109 + z * (148 + z * (93 + z * (50 + z * (85 + z * (57 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow12_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_64 z * u11 z = pow12_65_q z * f z + pow12_65 z + (131 : R) * pow12_65_mul_t z := by
  simp only [pow12_64, u11, pow12_65_q, f, pow12_65, pow12_65_mul_t]
  simp only [pow11_131]
  ring

theorem pow12_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_64 z * u11 z = pow12_65_q z * f z + pow12_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_65_mul_integer z


theorem pow12_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_64 z * u11 z = pow12_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_65_mul z


theorem pow12_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 65 = pow12_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow12_64_pow z hz]
  exact pow12_65_root z hz


def pow12_130 {R : Type*} [CommRing R] (z : R) : R := (88 + z * (23 + z * (73 + z * (10 + z * (28 + z * (71 + z * (8 + z * (15 + z * (75 + z * (66 + z * (83 + z * (122 + z * (75 + z * (129 + z * (120 + z * (82 + z * (51 + z * (74 + z * (77 + z * 40)))))))))))))))))))

def pow12_130_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (101 + z * (65 + z * (98 + z * (35 + z * (64 + z * (31 + z * (26 + z * (40 + z * (92 + z * (42 + z * (106 + z * (19 + z * (13 + z * (41 + z * (23 + z * (38 + z * (92 + z * 89))))))))))))))))))

def pow12_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-6) + z * (14 + z * ((-98) + z * ((-25) + z * ((-12) + z * (43 + z * ((-41) + z * ((-58) + z * ((-69) + z * ((-56) + z * ((-101) + z * ((-45) + z * ((-230) + z * ((-78) + z * ((-31) + z * ((-76) + z * (25 + z * (8 + z * (94 + z * ((-77) + z * ((-108) + z * ((-81) + z * (112 + z * (169 + z * (27 + z * ((-88) + z * (46 + z * ((-101) + z * (83 + z * (69 + z * (149 + z * (247 + z * ((-5) + z * (19 + z * (10 + z * (52 + z * (96 + z * 40))))))))))))))))))))))))))))))))))))))

theorem pow12_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_65 z * pow12_65 z = pow12_130_q z * f z + pow12_130 z + (131 : R) * pow12_130_mul_t z := by
  simp only [pow12_65, pow12_130_q, f, pow12_130, pow12_130_mul_t]
  
  ring

theorem pow12_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_65 z * pow12_65 z = pow12_130_q z * f z + pow12_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_130_mul_integer z


theorem pow12_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_65 z * pow12_65 z = pow12_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_130_mul z


theorem pow12_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 130 = pow12_130 z := by
  calc
    _ = u11 z ^ 65 * u11 z ^ 65 := by ring
    _ = pow12_65 z * pow12_65 z := by rw [pow12_65_pow z hz]
    _ = _ := pow12_130_root z hz


def pow12_131 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (57 + z * (55 + z * (73 + z * (5 + z * (71 + z * (56 + z * (76 + z * (10 + z * (77 + z * (114 + z * (21 + z * (33 + z * (61 + z * (48 + z * (71 + z * (34 + z * (111 + z * (63 + z * 80)))))))))))))))))))

def pow12_131_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (9 + z * (11 + z * (104 + z * (1 + z * (130 + z * (63 + z * (128 + z * (51 + z * (64 + z * (1 + z * (47 + z * (125 + z * (17 + z * (109 + z * (18 + z * (124 + z * (66 + z * 33))))))))))))))))))

def pow12_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (65 + z * (40 + z * (80 + z * (16 + z * (74 + z * (5 + z * (30 + z * ((-105) + z * ((-36) + z * ((-4) + z * ((-55) + z * ((-21) + z * (16 + z * (83 + z * (13 + z * (150 + z * ((-116) + z * (74 + z * (81 + z * (33 + z * (30 + z * (40 + z * (43 + z * (77 + z * (42 + z * (19 + z * (230 + z * (204 + z * (192 + z * (218 + z * (219 + z * (224 + z * (210 + z * (116 + z * (74 + z * (46 + z * (103 + z * (90 + z * 37))))))))))))))))))))))))))))))))))))))

theorem pow12_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_130 z * u11 z = pow12_131_q z * f z + pow12_131 z + (131 : R) * pow12_131_mul_t z := by
  simp only [pow12_130, u11, pow12_131_q, f, pow12_131, pow12_131_mul_t]
  simp only [pow11_131]
  ring

theorem pow12_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow12_130 z * u11 z = pow12_131_q z * f z + pow12_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow12_131_mul_integer z


theorem pow12_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow12_130 z * u11 z = pow12_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_131_mul z


theorem pow12_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u11 z ^ 131 = pow12_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow12_130_pow z hz]
  exact pow12_131_root z hz


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_131 z

theorem iterate12 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 12) = u12 z := by
  calc
    _ = (z ^ (131 ^ 11)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate11 z hz)
    _ = _ := pow12_131_pow z hz

end DimensionTen.Mod131

end

end OAI
