import OAI.Analysis.Quantum.DimensionTen.Mod139Powers09

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow19_2 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (51 + z * (73 + z * (77 + z * (15 + z * (121 + z * (90 + z * (94 + z * (69 + z * (21 + z * (21 + z * (113 + z * (100 + z * (101 + z * (52 + z * (54 + z * (135 + z * (127 + z * (126 + z * 87)))))))))))))))))))

def pow19_2_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (57 + z * (118 + z * (135 + z * (118 + z * (113 + z * (62 + z * (20 + z * (25 + z * (116 + z * (99 + z * (116 + z * (132 + z * (137 + z * (90 + z * (138 + z * (55 + z * (32 + z * 54))))))))))))))))))

def pow19_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (43 + z * ((-116) + z * ((-23) + z * ((-239) + z * ((-99) + z * ((-262) + z * ((-192) + z * ((-226) + z * ((-32) + z * ((-84) + z * ((-197) + z * ((-179) + z * ((-171) + z * ((-392) + z * ((-239) + z * ((-302) + z * ((-238) + z * ((-230) + z * ((-149) + z * ((-289) + z * ((-21) + z * ((-188) + z * ((-212) + z * ((-83) + z * ((-34) + z * ((-163) + z * (6 + z * (81 + z * ((-151) + z * ((-130) + z * (31 + z * ((-111) + z * ((-64) + z * (11 + z * (16 + z * (2 + z * (19 + z * (8 + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow19_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z + (139 : R) * pow19_2_mul_t z := by
  simp only [u18, pow19_2_q, f, pow19_2, pow19_2_mul_t]
  simp only [pow18_139]
  ring

theorem pow19_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_2_mul_integer z


theorem pow19_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z * u18 z = pow19_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_2_mul z


theorem pow19_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 2 = pow19_2 z := by
  calc
    _ = u18 z ^ 1 * u18 z ^ 1 := by ring
    _ = u18 z * u18 z := by simp only [pow_one]
    _ = _ := pow19_2_root z hz


def pow19_4 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (47 + z * (66 + z * (32 + z * (126 + z * (130 + z * (110 + z * (31 + z * (27 + z * (78 + z * (103 + z * (47 + z * (110 + z * (28 + z * (1 + z * (8 + z * (25 + z * (44 + z * (97 + z * 117)))))))))))))))))))

def pow19_4_q {R : Type*} [CommRing R] (z : R) : R := (87 + z * (47 + z * (74 + z * (107 + z * (3 + z * (74 + z * (95 + z * (69 + z * (67 + z * (136 + z * (1 + z * (58 + z * (45 + z * (99 + z * (65 + z * (52 + z * (111 + z * (99 + z * 63))))))))))))))))))

def pow19_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-110) + z * ((-154) + z * ((-214) + z * ((-181) + z * ((-192) + z * ((-193) + z * ((-162) + z * ((-100) + z * ((-276) + z * ((-253) + z * ((-234) + z * ((-191) + z * ((-163) + z * ((-76) + z * ((-283) + z * ((-331) + z * ((-157) + z * ((-105) + z * ((-28) + z * (95 + z * (28 + z * (92 + z * (311 + z * (273 + z * (102 + z * (39 + z * (6 + z * (149 + z * (318 + z * (301 + z * (179 + z * (129 + z * (188 + z * (246 + z * (224 + z * (135 + z * (99 + z * 54))))))))))))))))))))))))))))))))))))))

theorem pow19_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z + (139 : R) * pow19_4_mul_t z := by
  simp only [pow19_2, pow19_4_q, f, pow19_4, pow19_4_mul_t]
  
  ring

theorem pow19_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_4_mul_integer z


theorem pow19_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_2 z * pow19_2 z = pow19_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_4_mul z


theorem pow19_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 4 = pow19_4 z := by
  calc
    _ = u18 z ^ 2 * u18 z ^ 2 := by ring
    _ = pow19_2 z * pow19_2 z := by rw [pow19_2_pow z hz]
    _ = _ := pow19_4_root z hz


def pow19_8 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (70 + z * (106 + z * (96 + z * (65 + z * (15 + z * (27 + z * (60 + z * (95 + z * (137 + z * (111 + z * (126 + z * (100 + z * (2 + z * (63 + z * (82 + z * (78 + z * (41 + z * (112 + z * 62)))))))))))))))))))

def pow19_8_q {R : Type*} [CommRing R] (z : R) : R := (77 + z * (23 + z * (52 + z * (18 + z * (46 + z * (98 + z * (78 + z * (118 + z * (3 + z * (92 + z * (30 + z * (53 + z * (63 + z * (106 + z * (1 + z * (57 + z * (23 + z * (83 + z * 67))))))))))))))))))

def pow19_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-42) + z * ((-53) + z * ((-68) + z * ((-87) + z * ((-40) + z * ((-16) + z * (13 + z * ((-93) + z * ((-67) + z * ((-70) + z * (25 + z * (28 + z * ((-9) + z * ((-143) + z * ((-34) + z * ((-138) + z * ((-99) + z * ((-124) + z * ((-192) + z * ((-250) + z * ((-231) + z * ((-96) + z * ((-2) + z * (88 + z * (76 + z * ((-191) + z * ((-251) + z * ((-109) + z * ((-23) + z * (82 + z * (15 + z * ((-68) + z * ((-141) + z * ((-127) + z * ((-63) + z * (21 + z * (16 + z * (101 + z * 98))))))))))))))))))))))))))))))))))))))

theorem pow19_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_4 z * pow19_4 z = pow19_8_q z * f z + pow19_8 z + (139 : R) * pow19_8_mul_t z := by
  simp only [pow19_4, pow19_8_q, f, pow19_8, pow19_8_mul_t]
  
  ring

theorem pow19_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_4 z * pow19_4 z = pow19_8_q z * f z + pow19_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_8_mul_integer z


theorem pow19_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_4 z * pow19_4 z = pow19_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_8_mul z


theorem pow19_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 8 = pow19_8 z := by
  calc
    _ = u18 z ^ 4 * u18 z ^ 4 := by ring
    _ = pow19_4 z * pow19_4 z := by rw [pow19_4_pow z hz]
    _ = _ := pow19_8_root z hz


def pow19_16 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (23 + z * (52 + z * (49 + z * (30 + z * (134 + z * (23 + z * (90 + z * (87 + z * (124 + z * (96 + z * (67 + z * (20 + z * (64 + z * (126 + z * (48 + z * (96 + z * (15 + z * (136 + z * 134)))))))))))))))))))

def pow19_16_q {R : Type*} [CommRing R] (z : R) : R := (127 + z * (5 + z * (40 + z * (127 + z * (17 + z * (58 + z * (45 + z * (21 + z * (43 + z * (39 + z * (20 + z * (106 + z * (135 + z * (92 + z * (129 + z * (44 + z * (43 + z * (16 + z * 91))))))))))))))))))

def pow19_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-73) + z * ((-58) + z * ((-27) + z * ((-71) + z * ((-34) + z * ((-30) + z * ((-95) + z * ((-119) + z * ((-56) + z * ((-7) + z * (95 + z * (245 + z * (147 + z * ((-59) + z * ((-66) + z * ((-198) + z * ((-197) + z * (105 + z * (89 + z * (153 + z * (311 + z * (52 + z * (2 + z * (109 + z * (0 + z * (115 + z * (225 + z * (116 + z * (98 + z * (99 + z * (6 + z * ((-127) + z * ((-69) + z * (11 + z * (62 + z * (84 + z * (45 + z * (16 + z * 27))))))))))))))))))))))))))))))))))))))

theorem pow19_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_8 z * pow19_8 z = pow19_16_q z * f z + pow19_16 z + (139 : R) * pow19_16_mul_t z := by
  simp only [pow19_8, pow19_16_q, f, pow19_16, pow19_16_mul_t]
  
  ring

theorem pow19_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_8 z * pow19_8 z = pow19_16_q z * f z + pow19_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_16_mul_integer z


theorem pow19_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_8 z * pow19_8 z = pow19_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_16_mul z


theorem pow19_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 16 = pow19_16 z := by
  calc
    _ = u18 z ^ 8 * u18 z ^ 8 := by ring
    _ = pow19_8 z * pow19_8 z := by rw [pow19_8_pow z hz]
    _ = _ := pow19_16_root z hz


def pow19_17 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (46 + z * (3 + z * (138 + z * (110 + z * (38 + z * (135 + z * (86 + z * (46 + z * (90 + z * (57 + z * (5 + z * (98 + z * (36 + z * (14 + z * (94 + z * (79 + z * (81 + z * (15 + z * 52)))))))))))))))))))

def pow19_17_q {R : Type*} [CommRing R] (z : R) : R := (114 + z * (2 + z * (73 + z * (79 + z * (63 + z * (97 + z * (71 + z * (7 + z * (108 + z * (9 + z * (84 + z * (112 + z * (107 + z * (58 + z * (12 + z * (10 + z * (52 + z * (46 + z * 88))))))))))))))))))

def pow19_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-76) + z * ((-60) + z * ((-143) + z * ((-133) + z * ((-65) + z * ((-212) + z * ((-64) + z * ((-134) + z * (7 + z * ((-83) + z * ((-24) + z * ((-161) + z * ((-157) + z * ((-18) + z * ((-112) + z * (39 + z * (114 + z * (81 + z * (63 + z * (119 + z * (5 + z * (178 + z * (329 + z * (118 + z * (194 + z * (108 + z * (128 + z * (221 + z * (144 + z * (140 + z * (71 + z * (125 + z * (170 + z * (194 + z * (68 + z * (14 + z * (58 + z * 36))))))))))))))))))))))))))))))))))))))

theorem pow19_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_16 z * u18 z = pow19_17_q z * f z + pow19_17 z + (139 : R) * pow19_17_mul_t z := by
  simp only [pow19_16, u18, pow19_17_q, f, pow19_17, pow19_17_mul_t]
  simp only [pow18_139]
  ring

theorem pow19_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_16 z * u18 z = pow19_17_q z * f z + pow19_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_17_mul_integer z


theorem pow19_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_16 z * u18 z = pow19_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_17_mul z


theorem pow19_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 17 = pow19_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow19_16_pow z hz]
  exact pow19_17_root z hz


def pow19_34 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (104 + z * (104 + z * (74 + z * (66 + z * (16 + z * (1 + z * (86 + z * (109 + z * (51 + z * (24 + z * (66 + z * (105 + z * (50 + z * (129 + z * (80 + z * (17 + z * (32 + z * (50 + z * 108)))))))))))))))))))

def pow19_34_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (86 + z * (116 + z * (82 + z * (130 + z * (134 + z * (87 + z * (124 + z * (127 + z * (21 + z * (60 + z * (71 + z * (48 + z * (72 + z * (122 + z * (66 + z * (40 + z * (29 + z * 63))))))))))))))))))

def pow19_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (98 + z * ((-6) + z * ((-170) + z * ((-10) + z * ((-83) + z * ((-326) + z * ((-86) + z * ((-90) + z * ((-331) + z * ((-102) + z * ((-100) + z * ((-372) + z * ((-79) + z * ((-125) + z * ((-517) + z * ((-255) + z * ((-210) + z * ((-471) + z * ((-315) + z * ((-118) + z * ((-372) + z * ((-302) + z * ((-135) + z * ((-297) + z * ((-248) + z * ((-93) + z * ((-255) + z * ((-209) + z * ((-94) + z * ((-114) + z * ((-158) + z * ((-45) + z * ((-50) + z * ((-103) + z * ((-9) + z * (18 + z * ((-11) + z * ((-47) + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow19_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_17 z * pow19_17 z = pow19_34_q z * f z + pow19_34 z + (139 : R) * pow19_34_mul_t z := by
  simp only [pow19_17, pow19_34_q, f, pow19_34, pow19_34_mul_t]
  
  ring

theorem pow19_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_17 z * pow19_17 z = pow19_34_q z * f z + pow19_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_34_mul_integer z


theorem pow19_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_17 z * pow19_17 z = pow19_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_34_mul z


theorem pow19_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 34 = pow19_34 z := by
  calc
    _ = u18 z ^ 17 * u18 z ^ 17 := by ring
    _ = pow19_17 z * pow19_17 z := by rw [pow19_17_pow z hz]
    _ = _ := pow19_34_root z hz


def pow19_68 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (123 + z * (75 + z * (82 + z * (9 + z * (20 + z * (113 + z * (88 + z * (64 + z * (35 + z * (136 + z * (122 + z * (16 + z * (3 + z * (73 + z * (65 + z * (51 + z * (38 + z * (73 + z * 43)))))))))))))))))))

def pow19_68_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (64 + z * (66 + z * (37 + z * (126 + z * (129 + z * (50 + z * (79 + z * (133 + z * (122 + z * (1 + z * (5 + z * (123 + z * (22 + z * (68 + z * (49 + z * (104 + z * (104 + z * 127))))))))))))))))))

def pow19_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (123 + z * (143 + z * (127 + z * (45 + z * ((-122) + z * ((-215) + z * ((-169) + z * ((-139) + z * ((-169) + z * ((-181) + z * ((-146) + z * ((-112) + z * ((-140) + z * ((-40) + z * (24 + z * ((-81) + z * ((-343) + z * ((-442) + z * ((-193) + z * ((-283) + z * ((-238) + z * ((-186) + z * ((-209) + z * ((-332) + z * ((-259) + z * ((-6) + z * ((-167) + z * ((-148) + z * (55 + z * ((-76) + z * ((-121) + z * ((-68) + z * ((-1) + z * ((-84) + z * ((-123) + z * ((-122) + z * ((-40) + z * 83))))))))))))))))))))))))))))))))))))))

theorem pow19_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_34 z * pow19_34 z = pow19_68_q z * f z + pow19_68 z + (139 : R) * pow19_68_mul_t z := by
  simp only [pow19_34, pow19_68_q, f, pow19_68, pow19_68_mul_t]
  
  ring

theorem pow19_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_34 z * pow19_34 z = pow19_68_q z * f z + pow19_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_68_mul_integer z


theorem pow19_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_34 z * pow19_34 z = pow19_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_68_mul z


theorem pow19_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 68 = pow19_68 z := by
  calc
    _ = u18 z ^ 34 * u18 z ^ 34 := by ring
    _ = pow19_34 z * pow19_34 z := by rw [pow19_34_pow z hz]
    _ = _ := pow19_68_root z hz


def pow19_69 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (109 + z * (120 + z * (83 + z * (96 + z * (23 + z * (17 + z * (113 + z * (97 + z * (28 + z * (15 + z * (82 + z * (12 + z * (14 + z * (15 + z * (53 + z * (85 + z * (74 + z * (115 + z * 70)))))))))))))))))))

def pow19_69_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (109 + z * (5 + z * (17 + z * (35 + z * (29 + z * (101 + z * (105 + z * (112 + z * (49 + z * (116 + z * (53 + z * (3 + z * (63 + z * (34 + z * (89 + z * (135 + z * (8 + z * 105))))))))))))))))))

def pow19_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * ((-12) + z * (59 + z * ((-10) + z * (87 + z * (99 + z * ((-17) + z * ((-115) + z * ((-118) + z * ((-28) + z * ((-34) + z * (70 + z * (14 + z * (3 + z * (80 + z * ((-97) + z * ((-154) + z * (17 + z * ((-54) + z * ((-128) + z * (26 + z * (40 + z * ((-72) + z * ((-96) + z * ((-106) + z * ((-79) + z * ((-14) + z * ((-78) + z * ((-68) + z * (58 + z * ((-127) + z * ((-64) + z * (21 + z * ((-114) + z * ((-49) + z * ((-15) + z * ((-44) + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow19_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_68 z * u18 z = pow19_69_q z * f z + pow19_69 z + (139 : R) * pow19_69_mul_t z := by
  simp only [pow19_68, u18, pow19_69_q, f, pow19_69, pow19_69_mul_t]
  simp only [pow18_139]
  ring

theorem pow19_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_68 z * u18 z = pow19_69_q z * f z + pow19_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_69_mul_integer z


theorem pow19_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_68 z * u18 z = pow19_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_69_mul z


theorem pow19_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 69 = pow19_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow19_68_pow z hz]
  exact pow19_69_root z hz


def pow19_138 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (77 + z * (67 + z * (14 + z * (71 + z * (65 + z * (45 + z * (126 + z * (111 + z * (28 + z * (64 + z * (46 + z * (104 + z * (33 + z * (118 + z * (3 + z * (105 + z * (87 + z * (137 + z * 100)))))))))))))))))))

def pow19_138_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (2 + z * (58 + z * (42 + z * (70 + z * (116 + z * (34 + z * (86 + z * (17 + z * (23 + z * (23 + z * (77 + z * (65 + z * (76 + z * (75 + z * (45 + z * (78 + z * (83 + z * 35))))))))))))))))))

def pow19_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (121 + z * (180 + z * (176 + z * (197 + z * (67 + z * ((-22) + z * (18 + z * (108 + z * (81 + z * (47 + z * (128 + z * ((-44) + z * ((-227) + z * ((-266) + z * ((-198) + z * ((-187) + z * ((-153) + z * (9 + z * (111 + z * ((-50) + z * ((-150) + z * ((-49) + z * ((-155) + z * ((-157) + z * ((-61) + z * ((-65) + z * ((-108) + z * ((-119) + z * ((-117) + z * ((-173) + z * ((-155) + z * ((-111) + z * ((-1) + z * (105 + z * (75 + z * (67 + z * (83 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow19_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_69 z * pow19_69 z = pow19_138_q z * f z + pow19_138 z + (139 : R) * pow19_138_mul_t z := by
  simp only [pow19_69, pow19_138_q, f, pow19_138, pow19_138_mul_t]
  
  ring

theorem pow19_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_69 z * pow19_69 z = pow19_138_q z * f z + pow19_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_138_mul_integer z


theorem pow19_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_69 z * pow19_69 z = pow19_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_138_mul z


theorem pow19_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 138 = pow19_138 z := by
  calc
    _ = u18 z ^ 69 * u18 z ^ 69 := by ring
    _ = pow19_69 z * pow19_69 z := by rw [pow19_69_pow z hz]
    _ = _ := pow19_138_root z hz


abbrev pow19_139 {R : Type*} [CommRing R] (z : R) : R := u0 z

def pow19_139_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (113 + z * (84 + z * (90 + z * (97 + z * (114 + z * (3 + z * (97 + z * (33 + z * (100 + z * (76 + z * (99 + z * (94 + z * (13 + z * (49 + z * (96 + z * (82 + z * (60 + z * 47))))))))))))))))))

def pow19_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * ((-120) + z * ((-110) + z * ((-239) + z * ((-163) + z * ((-218) + z * ((-165) + z * ((-179) + z * ((-119) + z * ((-134) + z * ((-183) + z * ((-226) + z * ((-98) + z * ((-299) + z * ((-156) + z * ((-228) + z * (22 + z * ((-181) + z * ((-96) + z * ((-157) + z * ((-76) + z * ((-12) + z * (133 + z * (114 + z * ((-6) + z * ((-22) + z * (134 + z * (82 + z * (100 + z * (101 + z * (70 + z * (34 + z * (171 + z * (90 + z * (97 + z * (62 + z * (48 + z * (70 + z * 27))))))))))))))))))))))))))))))))))))))

theorem pow19_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_138 z * u18 z = pow19_139_q z * f z + pow19_139 z + (139 : R) * pow19_139_mul_t z := by
  simp only [pow19_138, u18, pow19_139_q, f, pow19_139, pow19_139_mul_t]
  simp only [pow18_139, u0]
  ring

theorem pow19_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow19_138 z * u18 z = pow19_139_q z * f z + pow19_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow19_139_mul_integer z


theorem pow19_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow19_138 z * u18 z = pow19_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_139_mul z


theorem pow19_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u18 z ^ 139 = pow19_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow19_138_pow z hz]
  exact pow19_139_root z hz


abbrev u19 {R : Type*} [CommRing R] (z : R) : R := u0 z

theorem iterate19 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 19) = u19 z := by
  calc
    _ = (z ^ (139 ^ 18)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u18 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate18 z hz)
    _ = _ := pow19_139_pow z hz

end DimensionTen.Mod139

end

end OAI
