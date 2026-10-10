import OAI.Analysis.Quantum.DimensionTen.Mod131Powers07

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow15_2 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (94 + z * (7 + z * (14 + z * (120 + z * (42 + z * (14 + z * (62 + z * (41 + z * (103 + z * (0 + z * (112 + z * (113 + z * (34 + z * (30 + z * (11 + z * (120 + z * (44 + z * (91 + z * 24)))))))))))))))))))

def pow15_2_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (92 + z * (110 + z * (52 + z * (65 + z * (77 + z * (27 + z * (22 + z * (68 + z * (86 + z * (20 + z * (124 + z * (92 + z * (71 + z * (125 + z * (5 + z * (1 + z * (54 + z * 5))))))))))))))))))

def pow15_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (45 + z * (74 + z * (20 + z * (78 + z * (139 + z * (55 + z * (24 + z * (138 + z * (66 + z * ((-107) + z * (90 + z * (106 + z * ((-71) + z * ((-160) + z * ((-46) + z * (21 + z * ((-24) + z * (109 + z * (103 + z * (60 + z * (52 + z * (47 + z * (46 + z * ((-13) + z * ((-75) + z * (1 + z * (87 + z * (47 + z * (50 + z * (1 + z * ((-27) + z * (94 + z * (133 + z * (142 + z * (164 + z * (90 + z * (35 + z * (22 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow15_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z + (131 : R) * pow15_2_mul_t z := by
  simp only [u14, pow15_2_q, f, pow15_2, pow15_2_mul_t]
  simp only [pow14_131]
  ring

theorem pow15_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_2_mul_integer z


theorem pow15_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z * u14 z = pow15_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_2_mul z


theorem pow15_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 2 = pow15_2 z := by
  calc
    _ = u14 z ^ 1 * u14 z ^ 1 := by ring
    _ = u14 z * u14 z := by simp only [pow_one]
    _ = _ := pow15_2_root z hz


def pow15_4 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (8 + z * (116 + z * (9 + z * (124 + z * (103 + z * (48 + z * (27 + z * (31 + z * (64 + z * (105 + z * (30 + z * (11 + z * (2 + z * (78 + z * (112 + z * (90 + z * (129 + z * (59 + z * 98)))))))))))))))))))

def pow15_4_q {R : Type*} [CommRing R] (z : R) : R := (128 + z * (114 + z * (60 + z * (86 + z * (115 + z * (122 + z * (118 + z * (63 + z * (46 + z * (127 + z * (64 + z * (104 + z * (25 + z * (127 + z * (40 + z * (55 + z * (45 + z * (19 + z * 52))))))))))))))))))

def pow15_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-12) + z * ((-54) + z * ((-111) + z * ((-75) + z * ((-106) + z * ((-208) + z * ((-214) + z * ((-173) + z * ((-226) + z * ((-227) + z * ((-317) + z * ((-170) + z * ((-216) + z * ((-402) + z * ((-243) + z * ((-167) + z * ((-265) + z * ((-287) + z * ((-219) + z * ((-87) + z * ((-188) + z * ((-204) + z * ((-18) + z * ((-147) + z * (4 + z * ((-148) + z * (88 + z * (61 + z * (27 + z * (76 + z * ((-37) + z * (31 + z * (17 + z * (96 + z * (54 + z * (46 + z * (7 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (131 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

theorem pow15_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_4_mul_integer z


theorem pow15_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_2 z * pow15_2 z = pow15_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_4_mul z


theorem pow15_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 4 = pow15_4 z := by
  calc
    _ = u14 z ^ 2 * u14 z ^ 2 := by ring
    _ = pow15_2 z * pow15_2 z := by rw [pow15_2_pow z hz]
    _ = _ := pow15_4_root z hz


def pow15_8 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (0 + z * (74 + z * (40 + z * (121 + z * (10 + z * (58 + z * (66 + z * (39 + z * (35 + z * (123 + z * (43 + z * (44 + z * (117 + z * (10 + z * (78 + z * (81 + z * (15 + z * (8 + z * 12)))))))))))))))))))

def pow15_8_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (117 + z * (4 + z * (32 + z * (68 + z * (7 + z * (67 + z * (93 + z * (38 + z * (58 + z * (103 + z * (78 + z * (1 + z * (115 + z * (0 + z * (116 + z * (40 + z * (81 + z * 41))))))))))))))))))

def pow15_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-45) + z * (41 + z * ((-53) + z * (133 + z * ((-9) + z * (100 + z * (119 + z * (21 + z * (49 + z * (113 + z * ((-24) + z * ((-51) + z * ((-71) + z * (39 + z * ((-62) + z * (34 + z * ((-43) + z * ((-41) + z * (311 + z * (139 + z * (333 + z * (9 + z * (136 + z * (143 + z * (109 + z * ((-13) + z * (93 + z * (5 + z * (60 + z * (69 + z * (157 + z * (203 + z * (262 + z * (242 + z * (178 + z * (160 + z * (67 + z * 73))))))))))))))))))))))))))))))))))))))

theorem pow15_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z + (131 : R) * pow15_8_mul_t z := by
  simp only [pow15_4, pow15_8_q, f, pow15_8, pow15_8_mul_t]
  
  ring

theorem pow15_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_8_mul_integer z


theorem pow15_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_4 z * pow15_4 z = pow15_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_8_mul z


theorem pow15_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 8 = pow15_8 z := by
  calc
    _ = u14 z ^ 4 * u14 z ^ 4 := by ring
    _ = pow15_4 z * pow15_4 z := by rw [pow15_4_pow z hz]
    _ = _ := pow15_8_root z hz


def pow15_16 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (34 + z * (100 + z * (43 + z * (14 + z * (12 + z * (116 + z * (123 + z * (64 + z * (98 + z * (111 + z * (41 + z * (45 + z * (123 + z * (48 + z * (98 + z * (12 + z * (116 + z * (15 + z * 105)))))))))))))))))))

def pow15_16_q {R : Type*} [CommRing R] (z : R) : R := (48 + z * (59 + z * (73 + z * (93 + z * (127 + z * (90 + z * (73 + z * (38 + z * (41 + z * (64 + z * (81 + z * (16 + z * (22 + z * (48 + z * (11 + z * (105 + z * (121 + z * (120 + z * 13))))))))))))))))))

def pow15_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-40) + z * ((-45) + z * ((-84) + z * ((-66) + z * ((-163) + z * ((-60) + z * ((-138) + z * ((-102) + z * ((-194) + z * ((-98) + z * ((-168) + z * ((-113) + z * ((-126) + z * ((-52) + z * ((-120) + z * ((-127) + z * ((-77) + z * ((-191) + z * ((-46) + z * ((-89) + z * ((-262) + z * ((-164) + z * (0 + z * ((-186) + z * ((-49) + z * (15 + z * ((-139) + z * ((-126) + z * ((-63) + z * ((-60) + z * ((-33) + z * ((-92) + z * ((-151) + z * ((-135) + z * ((-104) + z * ((-64) + z * ((-6) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow15_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z + (131 : R) * pow15_16_mul_t z := by
  simp only [pow15_8, pow15_16_q, f, pow15_16, pow15_16_mul_t]
  
  ring

theorem pow15_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_16_mul_integer z


theorem pow15_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_8 z * pow15_8 z = pow15_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_16_mul z


theorem pow15_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 16 = pow15_16 z := by
  calc
    _ = u14 z ^ 8 * u14 z ^ 8 := by ring
    _ = pow15_8 z * pow15_8 z := by rw [pow15_8_pow z hz]
    _ = _ := pow15_16_root z hz


def pow15_32 {R : Type*} [CommRing R] (z : R) : R := (74 + z * (22 + z * (123 + z * (107 + z * (5 + z * (20 + z * (107 + z * (25 + z * (17 + z * (22 + z * (117 + z * (8 + z * (99 + z * (77 + z * (62 + z * (99 + z * (56 + z * (19 + z * (94 + z * 83)))))))))))))))))))

def pow15_32_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (66 + z * (79 + z * (115 + z * (33 + z * (78 + z * (83 + z * (68 + z * (112 + z * (121 + z * (8 + z * (115 + z * (68 + z * (33 + z * (29 + z * (96 + z * (63 + z * (61 + z * 21))))))))))))))))))

def pow15_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-22) + z * (7 + z * ((-28) + z * ((-34) + z * ((-130) + z * ((-52) + z * ((-74) + z * ((-26) + z * (57 + z * ((-31) + z * ((-116) + z * ((-12) + z * ((-29) + z * ((-47) + z * (175 + z * (9 + z * (131 + z * ((-33) + z * (177 + z * (52 + z * (207 + z * (97 + z * (209 + z * (120 + z * (240 + z * (271 + z * (124 + z * (147 + z * (149 + z * (176 + z * (46 + z * (257 + z * ((-7) + z * (149 + z * ((-22) + z * (147 + z * (13 + z * 84))))))))))))))))))))))))))))))))))))))

theorem pow15_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_16 z * pow15_16 z = pow15_32_q z * f z + pow15_32 z + (131 : R) * pow15_32_mul_t z := by
  simp only [pow15_16, pow15_32_q, f, pow15_32, pow15_32_mul_t]
  
  ring

theorem pow15_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_16 z * pow15_16 z = pow15_32_q z * f z + pow15_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_32_mul_integer z


theorem pow15_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_16 z * pow15_16 z = pow15_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_32_mul z


theorem pow15_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 32 = pow15_32 z := by
  calc
    _ = u14 z ^ 16 * u14 z ^ 16 := by ring
    _ = pow15_16 z * pow15_16 z := by rw [pow15_16_pow z hz]
    _ = _ := pow15_32_root z hz


def pow15_64 {R : Type*} [CommRing R] (z : R) : R := (63 + z * (0 + z * (110 + z * (79 + z * (117 + z * (77 + z * (40 + z * (120 + z * (34 + z * (24 + z * (9 + z * (8 + z * (104 + z * (28 + z * (32 + z * (8 + z * (112 + z * (91 + z * (44 + z * 97)))))))))))))))))))

def pow15_64_q {R : Type*} [CommRing R] (z : R) : R := (48 + z * (20 + z * (66 + z * (70 + z * (82 + z * (120 + z * (78 + z * (117 + z * (6 + z * (128 + z * (94 + z * (123 + z * (47 + z * (19 + z * (91 + z * (22 + z * (90 + z * (42 + z * 77))))))))))))))))))

def pow15_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (23 + z * (0 + z * (86 + z * (93 + z * (38 + z * (51 + z * (45 + z * ((-158) + z * (4 + z * ((-76) + z * ((-132) + z * ((-295) + z * (16 + z * ((-79) + z * ((-207) + z * ((-3) + z * ((-47) + z * ((-116) + z * ((-65) + z * ((-107) + z * ((-34) + z * ((-5) + z * ((-125) + z * ((-276) + z * (11 + z * (50 + z * ((-73) + z * ((-60) + z * (116 + z * (39 + z * (66 + z * (184 + z * (105 + z * (98 + z * (90 + z * (5 + z * (35 + z * (80 + z * 52))))))))))))))))))))))))))))))))))))))

theorem pow15_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_32 z * pow15_32 z = pow15_64_q z * f z + pow15_64 z + (131 : R) * pow15_64_mul_t z := by
  simp only [pow15_32, pow15_64_q, f, pow15_64, pow15_64_mul_t]
  
  ring

theorem pow15_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_32 z * pow15_32 z = pow15_64_q z * f z + pow15_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_64_mul_integer z


theorem pow15_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_32 z * pow15_32 z = pow15_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_64_mul z


theorem pow15_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 64 = pow15_64 z := by
  calc
    _ = u14 z ^ 32 * u14 z ^ 32 := by ring
    _ = pow15_32 z * pow15_32 z := by rw [pow15_32_pow z hz]
    _ = _ := pow15_64_root z hz


def pow15_65 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (124 + z * (57 + z * (108 + z * (92 + z * (113 + z * (12 + z * (129 + z * (59 + z * (114 + z * (122 + z * (76 + z * (49 + z * (7 + z * (91 + z * (53 + z * (47 + z * (46 + z * (37 + z * 32)))))))))))))))))))

def pow15_65_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (86 + z * (51 + z * (11 + z * (32 + z * (89 + z * (23 + z * (38 + z * (57 + z * (55 + z * (86 + z * (123 + z * (32 + z * (108 + z * (107 + z * (13 + z * (23 + z * (37 + z * 4))))))))))))))))))

def pow15_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * ((-4) + z * (28 + z * (106 + z * (141 + z * (118 + z * (116 + z * (214 + z * (159 + z * (64 + z * (66 + z * (55 + z * (10 + z * ((-90) + z * (17 + z * ((-39) + z * ((-29) + z * (99 + z * ((-2) + z * (180 + z * (170 + z * (18 + z * (82 + z * (138 + z * ((-23) + z * ((-105) + z * ((-27) + z * ((-13) + z * (38 + z * (0 + z * ((-17) + z * (87 + z * (69 + z * (115 + z * (192 + z * (141 + z * (74 + z * (58 + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow15_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_64 z * u14 z = pow15_65_q z * f z + pow15_65 z + (131 : R) * pow15_65_mul_t z := by
  simp only [pow15_64, u14, pow15_65_q, f, pow15_65, pow15_65_mul_t]
  simp only [pow14_131]
  ring

theorem pow15_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_64 z * u14 z = pow15_65_q z * f z + pow15_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_65_mul_integer z


theorem pow15_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_64 z * u14 z = pow15_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_65_mul z


theorem pow15_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 65 = pow15_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow15_64_pow z hz]
  exact pow15_65_root z hz


def pow15_130 {R : Type*} [CommRing R] (z : R) : R := (64 + z * (34 + z * (107 + z * (80 + z * (119 + z * (48 + z * (82 + z * (57 + z * (80 + z * (123 + z * (17 + z * (15 + z * (57 + z * (105 + z * (76 + z * (88 + z * (32 + z * (87 + z * (115 + z * 56)))))))))))))))))))

def pow15_130_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (95 + z * (116 + z * (58 + z * (112 + z * (1 + z * (103 + z * (99 + z * (12 + z * (29 + z * (55 + z * (63 + z * (17 + z * (74 + z * (32 + z * (25 + z * (85 + z * (22 + z * 107))))))))))))))))))

def pow15_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (56 + z * (138 + z * (88 + z * (162 + z * (195 + z * (235 + z * (151 + z * (210 + z * (278 + z * (239 + z * (515 + z * (306 + z * (401 + z * (225 + z * (392 + z * (298 + z * (327 + z * (340 + z * (187 + z * (322 + z * (143 + z * (226 + z * (92 + z * (51 + z * (173 + z * (74 + z * (84 + z * (35 + z * (82 + z * ((-65) + z * ((-26) + z * ((-29) + z * ((-20) + z * (3 + z * ((-61) + z * ((-44) + z * ((-27) + z * ((-36) + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow15_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_65 z * pow15_65 z = pow15_130_q z * f z + pow15_130 z + (131 : R) * pow15_130_mul_t z := by
  simp only [pow15_65, pow15_130_q, f, pow15_130, pow15_130_mul_t]
  
  ring

theorem pow15_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_65 z * pow15_65 z = pow15_130_q z * f z + pow15_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_130_mul_integer z


theorem pow15_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_65 z * pow15_65 z = pow15_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_130_mul z


theorem pow15_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 130 = pow15_130 z := by
  calc
    _ = u14 z ^ 65 * u14 z ^ 65 := by ring
    _ = pow15_65 z * pow15_65 z := by rw [pow15_65_pow z hz]
    _ = _ := pow15_130_root z hz


def pow15_131 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (61 + z * (96 + z * (109 + z * (106 + z * (28 + z * (97 + z * (18 + z * (30 + z * (26 + z * (21 + z * (64 + z * (44 + z * (127 + z * (31 + z * (62 + z * (41 + z * (68 + z * (30 + z * 76)))))))))))))))))))

def pow15_131_q {R : Type*} [CommRing R] (z : R) : R := (101 + z * (115 + z * (116 + z * (65 + z * (128 + z * (37 + z * (129 + z * (78 + z * (102 + z * (11 + z * (52 + z * (97 + z * (28 + z * (112 + z * (2 + z * (75 + z * (109 + z * (82 + z * 109))))))))))))))))))

def pow15_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * ((-12) + z * ((-16) + z * (47 + z * (41 + z * (1 + z * ((-5) + z * (39 + z * ((-71) + z * ((-19) + z * (27 + z * ((-138) + z * ((-91) + z * ((-126) + z * ((-6) + z * ((-111) + z * (6 + z * ((-70) + z * (6 + z * (66 + z * ((-16) + z * (7 + z * ((-17) + z * ((-51) + z * (5 + z * (37 + z * ((-95) + z * ((-33) + z * (33 + z * ((-25) + z * (52 + z * (39 + z * (53 + z * (96 + z * (29 + z * (29 + z * (18 + z * ((-5) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow15_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_130 z * u14 z = pow15_131_q z * f z + pow15_131 z + (131 : R) * pow15_131_mul_t z := by
  simp only [pow15_130, u14, pow15_131_q, f, pow15_131, pow15_131_mul_t]
  simp only [pow14_131]
  ring

theorem pow15_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow15_130 z * u14 z = pow15_131_q z * f z + pow15_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow15_131_mul_integer z


theorem pow15_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow15_130 z * u14 z = pow15_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_131_mul z


theorem pow15_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u14 z ^ 131 = pow15_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow15_130_pow z hz]
  exact pow15_131_root z hz


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_131 z

theorem iterate15 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 15) = u15 z := by
  calc
    _ = (z ^ (131 ^ 14)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u14 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate14 z hz)
    _ = _ := pow15_131_pow z hz


def pow16_2 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (1 + z * (57 + z * (42 + z * (48 + z * (64 + z * (62 + z * (42 + z * (5 + z * (27 + z * (52 + z * (57 + z * (119 + z * (76 + z * (37 + z * (96 + z * (62 + z * (100 + z * (24 + z * 72)))))))))))))))))))

def pow16_2_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (78 + z * (2 + z * (95 + z * (0 + z * (59 + z * (61 + z * (5 + z * (93 + z * (128 + z * (86 + z * (52 + z * (13 + z * (87 + z * (70 + z * (26 + z * (129 + z * (100 + z * 12))))))))))))))))))

def pow16_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (93 + z * (70 + z * (158 + z * (203 + z * (298 + z * (176 + z * (313 + z * (220 + z * (125 + z * (108 + z * (1 + z * (1 + z * (40 + z * (91 + z * ((-3) + z * (212 + z * (74 + z * (128 + z * ((-45) + z * (196 + z * ((-28) + z * ((-114) + z * ((-102) + z * (49 + z * ((-161) + z * ((-141) + z * ((-72) + z * ((-159) + z * ((-88) + z * ((-94) + z * (83 + z * (42 + z * (40 + z * ((-58) + z * (9 + z * ((-36) + z * (29 + z * (28 + z * 44))))))))))))))))))))))))))))))))))))))

theorem pow16_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z + (131 : R) * pow16_2_mul_t z := by
  simp only [u15, pow16_2_q, f, pow16_2, pow16_2_mul_t]
  simp only [pow15_131]
  ring

theorem pow16_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_2_mul_integer z


theorem pow16_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z * u15 z = pow16_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_2_mul z


theorem pow16_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 2 = pow16_2 z := by
  calc
    _ = u15 z ^ 1 * u15 z ^ 1 := by ring
    _ = u15 z * u15 z := by simp only [pow_one]
    _ = _ := pow16_2_root z hz


def pow16_4 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (12 + z * (122 + z * (50 + z * (23 + z * (98 + z * (127 + z * (10 + z * (67 + z * (61 + z * (68 + z * (120 + z * (59 + z * (53 + z * (34 + z * (7 + z * (110 + z * (83 + z * (64 + z * 32)))))))))))))))))))

def pow16_4_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (83 + z * (50 + z * (91 + z * (83 + z * (73 + z * (13 + z * (89 + z * (38 + z * (102 + z * (112 + z * (5 + z * (74 + z * (74 + z * (67 + z * (64 + z * (32 + z * (78 + z * 75))))))))))))))))))

def pow16_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (73 + z * ((-69) + z * (4 + z * ((-33) + z * ((-47) + z * ((-94) + z * ((-17) + z * ((-75) + z * ((-196) + z * ((-173) + z * ((-115) + z * ((-176) + z * ((-131) + z * ((-146) + z * ((-212) + z * ((-55) + z * ((-111) + z * ((-19) + z * ((-172) + z * ((-22) + z * ((-217) + z * ((-123) + z * ((-83) + z * ((-62) + z * (50 + z * ((-69) + z * ((-83) + z * (80 + z * (56 + z * (92 + z * (105 + z * (111 + z * (134 + z * (23 + z * (79 + z * (25 + z * (41 + z * ((-12) + z * 39))))))))))))))))))))))))))))))))))))))

theorem pow16_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z + (131 : R) * pow16_4_mul_t z := by
  simp only [pow16_2, pow16_4_q, f, pow16_4, pow16_4_mul_t]
  
  ring

theorem pow16_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_4_mul_integer z


theorem pow16_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_2 z * pow16_2 z = pow16_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_4_mul z


theorem pow16_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 4 = pow16_4 z := by
  calc
    _ = u15 z ^ 2 * u15 z ^ 2 := by ring
    _ = pow16_2 z * pow16_2 z := by rw [pow16_2_pow z hz]
    _ = _ := pow16_4_root z hz


def pow16_8 {R : Type*} [CommRing R] (z : R) : R := (76 + z * (82 + z * (96 + z * (27 + z * (29 + z * (7 + z * (108 + z * (70 + z * (120 + z * (44 + z * (103 + z * (81 + z * (86 + z * (38 + z * (36 + z * (116 + z * (74 + z * (110 + z * (96 + z * 58)))))))))))))))))))

def pow16_8_q {R : Type*} [CommRing R] (z : R) : R := (58 + z * (10 + z * (38 + z * (55 + z * (120 + z * (35 + z * (123 + z * (32 + z * (79 + z * (82 + z * (59 + z * (87 + z * (116 + z * (119 + z * (30 + z * (23 + z * (124 + z * (47 + z * 107))))))))))))))))))

def pow16_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (80 + z * ((-4) + z * (170 + z * (61 + z * (46 + z * (125 + z * (146 + z * (52 + z * (164 + z * ((-3) + z * (116 + z * (175 + z * (85 + z * (44 + z * (63 + z * ((-67) + z * (127 + z * ((-3) + z * (75 + z * (88 + z * ((-106) + z * ((-64) + z * (88 + z * ((-83) + z * ((-68) + z * ((-124) + z * ((-53) + z * (26 + z * (0 + z * ((-81) + z * ((-30) + z * ((-104) + z * ((-23) + z * (29 + z * (8 + z * (11 + z * ((-1) + z * ((-23) + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow16_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z + (131 : R) * pow16_8_mul_t z := by
  simp only [pow16_4, pow16_8_q, f, pow16_8, pow16_8_mul_t]
  
  ring

theorem pow16_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_8_mul_integer z


theorem pow16_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_4 z * pow16_4 z = pow16_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_8_mul z


theorem pow16_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 8 = pow16_8 z := by
  calc
    _ = u15 z ^ 4 * u15 z ^ 4 := by ring
    _ = pow16_4 z * pow16_4 z := by rw [pow16_4_pow z hz]
    _ = _ := pow16_8_root z hz


def pow16_16 {R : Type*} [CommRing R] (z : R) : R := (75 + z * (4 + z * (114 + z * (95 + z * (48 + z * (95 + z * (20 + z * (45 + z * (5 + z * (5 + z * (120 + z * (111 + z * (96 + z * (91 + z * (38 + z * (61 + z * (87 + z * (15 + z * (89 + z * 65)))))))))))))))))))

def pow16_16_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (123 + z * (115 + z * (105 + z * (76 + z * (114 + z * (95 + z * (99 + z * (22 + z * (124 + z * (94 + z * (13 + z * (110 + z * (70 + z * (43 + z * (99 + z * (77 + z * (22 + z * 89))))))))))))))))))

def pow16_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (21 + z * (27 + z * (45 + z * ((-1) + z * ((-39) + z * ((-177) + z * ((-121) + z * ((-93) + z * (39 + z * ((-78) + z * ((-36) + z * ((-99) + z * ((-19) + z * ((-116) + z * ((-148) + z * ((-47) + z * (74 + z * (19 + z * (143 + z * (170 + z * ((-41) + z * (28 + z * (36 + z * (113 + z * (204 + z * (259 + z * (208 + z * (265 + z * (157 + z * (164 + z * (191 + z * (80 + z * (169 + z * (191 + z * (152 + z * (144 + z * (116 + z * (40 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow16_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z + (131 : R) * pow16_16_mul_t z := by
  simp only [pow16_8, pow16_16_q, f, pow16_16, pow16_16_mul_t]
  
  ring

theorem pow16_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_16_mul_integer z


theorem pow16_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_8 z * pow16_8 z = pow16_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_16_mul z


theorem pow16_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 16 = pow16_16 z := by
  calc
    _ = u15 z ^ 8 * u15 z ^ 8 := by ring
    _ = pow16_8 z * pow16_8 z := by rw [pow16_8_pow z hz]
    _ = _ := pow16_16_root z hz


def pow16_32 {R : Type*} [CommRing R] (z : R) : R := (127 + z * (98 + z * (25 + z * (87 + z * (17 + z * (5 + z * (43 + z * (44 + z * (12 + z * (19 + z * (116 + z * (12 + z * (26 + z * (109 + z * (38 + z * (122 + z * (73 + z * (11 + z * (75 + z * 68)))))))))))))))))))

def pow16_32_q {R : Type*} [CommRing R] (z : R) : R := (89 + z * (60 + z * (106 + z * (16 + z * (25 + z * (41 + z * (8 + z * (104 + z * (8 + z * (22 + z * (58 + z * (93 + z * (52 + z * (103 + z * (52 + z * (9 + z * (84 + z * (91 + z * 33))))))))))))))))))

def pow16_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-51) + z * (25 + z * (26 + z * (34 + z * (116 + z * (37 + z * (71 + z * (18 + z * ((-64) + z * (76 + z * ((-76) + z * (52 + z * (134 + z * (135 + z * (231 + z * (179 + z * (109 + z * (47 + z * ((-16) + z * (107 + z * (198 + z * (134 + z * (215 + z * (56 + z * (42 + z * (127 + z * (75 + z * (134 + z * (137 + z * (115 + z * (162 + z * (52 + z * (9 + z * (82 + z * (11 + z * (14 + z * (71 + z * 32))))))))))))))))))))))))))))))))))))))

theorem pow16_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_16 z * pow16_16 z = pow16_32_q z * f z + pow16_32 z + (131 : R) * pow16_32_mul_t z := by
  simp only [pow16_16, pow16_32_q, f, pow16_32, pow16_32_mul_t]
  
  ring

theorem pow16_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_16 z * pow16_16 z = pow16_32_q z * f z + pow16_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_32_mul_integer z


theorem pow16_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_16 z * pow16_16 z = pow16_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_32_mul z


theorem pow16_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 32 = pow16_32 z := by
  calc
    _ = u15 z ^ 16 * u15 z ^ 16 := by ring
    _ = pow16_16 z * pow16_16 z := by rw [pow16_16_pow z hz]
    _ = _ := pow16_32_root z hz


def pow16_64 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (103 + z * (69 + z * (106 + z * (23 + z * (57 + z * (8 + z * (43 + z * (86 + z * (22 + z * (11 + z * (2 + z * (129 + z * (44 + z * (45 + z * (4 + z * (74 + z * (21 + z * (102 + z * 42)))))))))))))))))))

def pow16_64_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (92 + z * (8 + z * (45 + z * (12 + z * (64 + z * (18 + z * (10 + z * (49 + z * (42 + z * (105 + z * (73 + z * (19 + z * (96 + z * (18 + z * (110 + z * (90 + z * (28 + z * 39))))))))))))))))))

def pow16_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (96 + z * (129 + z * (51 + z * (128 + z * (89 + z * ((-95) + z * (26 + z * (60 + z * ((-77) + z * ((-61) + z * (104 + z * (0 + z * ((-160) + z * (103 + z * (9 + z * (53 + z * (176 + z * ((-88) + z * ((-49) + z * (93 + z * ((-65) + z * ((-140) + z * ((-62) + z * ((-66) + z * ((-163) + z * (108 + z * ((-32) + z * ((-144) + z * (108 + z * (58 + z * (45 + z * (112 + z * (51 + z * (69 + z * (79 + z * (15 + z * (22 + z * (58 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow16_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_32 z * pow16_32 z = pow16_64_q z * f z + pow16_64 z + (131 : R) * pow16_64_mul_t z := by
  simp only [pow16_32, pow16_64_q, f, pow16_64, pow16_64_mul_t]
  
  ring

theorem pow16_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_32 z * pow16_32 z = pow16_64_q z * f z + pow16_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_64_mul_integer z


theorem pow16_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_32 z * pow16_32 z = pow16_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_64_mul z


theorem pow16_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 64 = pow16_64 z := by
  calc
    _ = u15 z ^ 32 * u15 z ^ 32 := by ring
    _ = pow16_32 z * pow16_32 z := by rw [pow16_32_pow z hz]
    _ = _ := pow16_64_root z hz


def pow16_65 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (12 + z * (82 + z * (12 + z * (13 + z * (106 + z * (129 + z * (64 + z * (117 + z * (97 + z * (105 + z * (41 + z * (73 + z * (24 + z * (85 + z * (5 + z * (3 + z * (98 + z * (115 + z * 100)))))))))))))))))))

def pow16_65_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (124 + z * (63 + z * (110 + z * (3 + z * (124 + z * (99 + z * (101 + z * (27 + z * (93 + z * (10 + z * (81 + z * (9 + z * (81 + z * (91 + z * (18 + z * (55 + z * (80 + z * 48))))))))))))))))))

def pow16_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * (29 + z * (25 + z * (101 + z * (96 + z * (14 + z * (8 + z * ((-24) + z * ((-98) + z * ((-87) + z * ((-189) + z * ((-196) + z * ((-122) + z * ((-182) + z * ((-124) + z * ((-52) + z * ((-71) + z * ((-194) + z * ((-144) + z * ((-159) + z * ((-12) + z * ((-110) + z * ((-159) + z * ((-112) + z * ((-143) + z * ((-126) + z * ((-132) + z * ((-17) + z * ((-87) + z * ((-7) + z * ((-59) + z * (127 + z * ((-14) + z * ((-11) + z * ((-14) + z * (32 + z * ((-5) + z * (44 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow16_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_64 z * u15 z = pow16_65_q z * f z + pow16_65 z + (131 : R) * pow16_65_mul_t z := by
  simp only [pow16_64, u15, pow16_65_q, f, pow16_65, pow16_65_mul_t]
  simp only [pow15_131]
  ring

theorem pow16_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_64 z * u15 z = pow16_65_q z * f z + pow16_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_65_mul_integer z


theorem pow16_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_64 z * u15 z = pow16_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_65_mul z


theorem pow16_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 65 = pow16_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow16_64_pow z hz]
  exact pow16_65_root z hz


def pow16_130 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (94 + z * (58 + z * (28 + z * (6 + z * (72 + z * (77 + z * (115 + z * (65 + z * (54 + z * (94 + z * (53 + z * (18 + z * (94 + z * (130 + z * (9 + z * (11 + z * (50 + z * (83 + z * 76)))))))))))))))))))

def pow16_130_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (7 + z * (83 + z * (2 + z * (38 + z * (26 + z * (49 + z * (91 + z * (88 + z * (32 + z * (38 + z * (91 + z * (88 + z * (76 + z * (60 + z * (103 + z * (7 + z * (53 + z * 44))))))))))))))))))

def pow16_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (10 + z * (109 + z * ((-1) + z * (7 + z * (152 + z * (182 + z * (120 + z * (273 + z * (125 + z * (280 + z * (209 + z * (253 + z * (101 + z * (381 + z * (124 + z * (194 + z * (271 + z * (280 + z * (304 + z * (164 + z * (99 + z * (99 + z * (170 + z * (288 + z * (207 + z * (171 + z * (249 + z * (186 + z * (106 + z * ((-12) + z * (81 + z * (67 + z * (16 + z * ((-18) + z * (132 + z * (204 + z * (153 + z * 76))))))))))))))))))))))))))))))))))))))

theorem pow16_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_65 z * pow16_65 z = pow16_130_q z * f z + pow16_130 z + (131 : R) * pow16_130_mul_t z := by
  simp only [pow16_65, pow16_130_q, f, pow16_130, pow16_130_mul_t]
  
  ring

theorem pow16_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_65 z * pow16_65 z = pow16_130_q z * f z + pow16_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_130_mul_integer z


theorem pow16_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_65 z * pow16_65 z = pow16_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_130_mul z


theorem pow16_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 130 = pow16_130 z := by
  calc
    _ = u15 z ^ 65 * u15 z ^ 65 := by ring
    _ = pow16_65 z * pow16_65 z := by rw [pow16_65_pow z hz]
    _ = _ := pow16_130_root z hz


def pow16_131 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (76 + z * (6 + z * (87 + z * (54 + z * (118 + z * (49 + z * (49 + z * (77 + z * (5 + z * (57 + z * (71 + z * (113 + z * (81 + z * (28 + z * (62 + z * (53 + z * (117 + z * (28 + z * 15)))))))))))))))))))

def pow16_131_q {R : Type*} [CommRing R] (z : R) : R := (55 + z * (22 + z * (46 + z * (87 + z * (118 + z * (22 + z * (76 + z * (66 + z * (6 + z * (3 + z * (16 + z * (44 + z * (10 + z * (53 + z * (32 + z * (116 + z * (40 + z * (67 + z * 12))))))))))))))))))

def pow16_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (82 + z * (86 + z * (99 + z * (54 + z * (62 + z * (85 + z * (107 + z * (46 + z * (119 + z * (197 + z * (82 + z * (91 + z * (240 + z * (243 + z * (22 + z * (120 + z * (135 + z * (163 + z * (137 + z * (189 + z * (174 + z * (60 + z * (86 + z * (126 + z * (137 + z * (91 + z * (134 + z * (23 + z * (90 + z * (95 + z * (86 + z * (79 + z * (25 + z * ((-14) + z * (29 + z * (48 + z * (59 + z * 44))))))))))))))))))))))))))))))))))))))

theorem pow16_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_130 z * u15 z = pow16_131_q z * f z + pow16_131 z + (131 : R) * pow16_131_mul_t z := by
  simp only [pow16_130, u15, pow16_131_q, f, pow16_131, pow16_131_mul_t]
  simp only [pow15_131]
  ring

theorem pow16_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow16_130 z * u15 z = pow16_131_q z * f z + pow16_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow16_131_mul_integer z


theorem pow16_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow16_130 z * u15 z = pow16_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_131_mul z


theorem pow16_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u15 z ^ 131 = pow16_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow16_130_pow z hz]
  exact pow16_131_root z hz


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_131 z

theorem iterate16 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 16) = u16 z := by
  calc
    _ = (z ^ (131 ^ 15)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u15 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate15 z hz)
    _ = _ := pow16_131_pow z hz

end DimensionTen.Mod131

end

end OAI
