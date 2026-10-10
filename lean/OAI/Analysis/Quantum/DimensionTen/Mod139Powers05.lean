import OAI.Analysis.Quantum.DimensionTen.Mod139Powers04

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow9_2 {R : Type*} [CommRing R] (z : R) : R := (73 + z * (45 + z * (77 + z * (120 + z * (43 + z * (71 + z * (112 + z * (119 + z * (118 + z * (35 + z * (137 + z * (58 + z * (86 + z * (110 + z * (56 + z * (137 + z * (97 + z * (6 + z * (76 + z * 50)))))))))))))))))))

def pow9_2_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (80 + z * (6 + z * (120 + z * (63 + z * (67 + z * (94 + z * (27 + z * (56 + z * (2 + z * (45 + z * (52 + z * (83 + z * (33 + z * (97 + z * (79 + z * (98 + z * (67 + z * 106))))))))))))))))))

def pow9_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * (63 + z * (40 + z * ((-156) + z * ((-153) + z * ((-84) + z * ((-129) + z * ((-154) + z * ((-52) + z * (98 + z * (99 + z * (61 + z * (24 + z * ((-16) + z * ((-1) + z * ((-101) + z * ((-126) + z * (164 + z * (25 + z * ((-97) + z * ((-17) + z * ((-8) + z * ((-48) + z * (98 + z * (26 + z * (75 + z * (174 + z * (70 + z * (83 + z * (93 + z * ((-66) + z * ((-50) + z * ((-25) + z * ((-27) + z * ((-27) + z * (21 + z * (18 + z * ((-57) + z * 50))))))))))))))))))))))))))))))))))))))

theorem pow9_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z + (139 : R) * pow9_2_mul_t z := by
  simp only [u8, pow9_2_q, f, pow9_2, pow9_2_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_2_mul_integer z


theorem pow9_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z * u8 z = pow9_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_2_mul z


theorem pow9_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 2 = pow9_2 z := by
  calc
    _ = u8 z ^ 1 * u8 z ^ 1 := by ring
    _ = u8 z * u8 z := by simp only [pow_one]
    _ = _ := pow9_2_root z hz


def pow9_4 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (104 + z * (2 + z * (138 + z * (117 + z * (20 + z * (2 + z * (120 + z * (57 + z * (10 + z * (38 + z * (10 + z * (59 + z * (73 + z * (44 + z * (101 + z * (117 + z * (92 + z * (81 + z * 38)))))))))))))))))))

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (30 + z * (27 + z * (70 + z * (131 + z * (138 + z * (67 + z * (132 + z * (2 + z * (72 + z * (133 + z * (59 + z * (21 + z * (98 + z * (120 + z * (126 + z * (5 + z * (72 + z * 137))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-62) + z * ((-92) + z * ((-70) + z * ((-54) + z * ((-152) + z * ((-136) + z * ((-117) + z * ((-204) + z * ((-72) + z * ((-73) + z * ((-31) + z * ((-13) + z * (29 + z * ((-1) + z * ((-103) + z * (28 + z * (51 + z * ((-17) + z * (67 + z * ((-117) + z * ((-20) + z * (183 + z * (87 + z * ((-12) + z * ((-5) + z * (79 + z * (106 + z * ((-17) + z * ((-24) + z * (3 + z * (4 + z * (20 + z * ((-66) + z * ((-153) + z * ((-30) + z * (18 + z * ((-121) + z * ((-72) + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow9_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z + (139 : R) * pow9_4_mul_t z := by
  simp only [pow9_2, pow9_4_q, f, pow9_4, pow9_4_mul_t]
  
  ring

theorem pow9_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_4_mul_integer z


theorem pow9_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_2 z * pow9_2 z = pow9_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_4_mul z


theorem pow9_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 4 = pow9_4 z := by
  calc
    _ = u8 z ^ 2 * u8 z ^ 2 := by ring
    _ = pow9_2 z * pow9_2 z := by rw [pow9_2_pow z hz]
    _ = _ := pow9_4_root z hz


def pow9_8 {R : Type*} [CommRing R] (z : R) : R := (118 + z * (38 + z * (115 + z * (109 + z * (64 + z * (70 + z * (13 + z * (6 + z * (72 + z * (55 + z * (135 + z * (85 + z * (87 + z * (60 + z * (123 + z * (30 + z * (125 + z * (37 + z * (123 + z * 4)))))))))))))))))))

def pow9_8_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (67 + z * (86 + z * (21 + z * (11 + z * (45 + z * (4 + z * (0 + z * (128 + z * (117 + z * (10 + z * (92 + z * (92 + z * (96 + z * (124 + z * (71 + z * (7 + z * (78 + z * 54))))))))))))))))))

def pow9_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-19) + z * ((-145) + z * ((-83) + z * (97 + z * ((-27) + z * ((-26) + z * (204 + z * (101 + z * ((-293) + z * ((-165) + z * ((-119) + z * ((-308) + z * ((-282) + z * ((-265) + z * ((-320) + z * ((-132) + z * ((-110) + z * ((-250) + z * (0 + z * (47 + z * ((-213) + z * ((-71) + z * ((-84) + z * ((-266) + z * ((-76) + z * ((-140) + z * ((-395) + z * ((-162) + z * ((-7) + z * ((-72) + z * (43 + z * (65 + z * (30 + z * (136 + z * (107 + z * ((-14) + z * ((-6) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow9_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z + (139 : R) * pow9_8_mul_t z := by
  simp only [pow9_4, pow9_8_q, f, pow9_8, pow9_8_mul_t]
  
  ring

theorem pow9_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_4 z * pow9_4 z = pow9_8_q z * f z + pow9_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_8_mul_integer z


theorem pow9_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_4 z * pow9_4 z = pow9_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_8_mul z


theorem pow9_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 8 = pow9_8 z := by
  calc
    _ = u8 z ^ 4 * u8 z ^ 4 := by ring
    _ = pow9_4 z * pow9_4 z := by rw [pow9_4_pow z hz]
    _ = _ := pow9_8_root z hz


def pow9_16 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (89 + z * (42 + z * (101 + z * (79 + z * (11 + z * (91 + z * (58 + z * (137 + z * (115 + z * (48 + z * (120 + z * (93 + z * (90 + z * (107 + z * (61 + z * (29 + z * (20 + z * (100 + z * 47)))))))))))))))))))

def pow9_16_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (125 + z * (55 + z * (45 + z * (80 + z * (125 + z * (95 + z * (126 + z * (136 + z * (71 + z * (113 + z * (6 + z * (35 + z * (92 + z * (136 + z * (107 + z * (4 + z * (48 + z * 16))))))))))))))))))

def pow9_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (78 + z * ((-56) + z * (28 + z * (25 + z * ((-28) + z * ((-30) + z * ((-136) + z * ((-245) + z * ((-313) + z * ((-413) + z * ((-286) + z * ((-273) + z * ((-43) + z * ((-33) + z * ((-127) + z * ((-296) + z * ((-149) + z * ((-376) + z * ((-23) + z * ((-120) + z * ((-112) + z * ((-54) + z * ((-111) + z * ((-296) + z * ((-135) + z * ((-112) + z * (90 + z * (11 + z * (157 + z * (29 + z * (154 + z * (4 + z * (124 + z * ((-128) + z * (117 + z * (33 + z * (55 + z * ((-8) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow9_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z + (139 : R) * pow9_16_mul_t z := by
  simp only [pow9_8, pow9_16_q, f, pow9_16, pow9_16_mul_t]
  
  ring

theorem pow9_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_8 z * pow9_8 z = pow9_16_q z * f z + pow9_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_16_mul_integer z


theorem pow9_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_8 z * pow9_8 z = pow9_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_16_mul z


theorem pow9_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 16 = pow9_16 z := by
  calc
    _ = u8 z ^ 8 * u8 z ^ 8 := by ring
    _ = pow9_8 z * pow9_8 z := by rw [pow9_8_pow z hz]
    _ = _ := pow9_16_root z hz


def pow9_17 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (56 + z * (36 + z * (60 + z * (15 + z * (77 + z * (75 + z * (21 + z * (33 + z * (95 + z * (113 + z * (45 + z * (76 + z * (98 + z * (0 + z * (104 + z * (131 + z * (39 + z * (72 + z * 120)))))))))))))))))))

def pow9_17_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (46 + z * (23 + z * (24 + z * (73 + z * (125 + z * (0 + z * (120 + z * (34 + z * (99 + z * (130 + z * (23 + z * (122 + z * (64 + z * (105 + z * (100 + z * (47 + z * (50 + z * 56))))))))))))))))))

def pow9_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-60) + z * ((-31) + z * ((-37) + z * ((-31) + z * ((-37) + z * ((-91) + z * ((-76) + z * ((-126) + z * ((-44) + z * ((-52) + z * ((-107) + z * ((-45) + z * ((-9) + z * ((-78) + z * ((-157) + z * ((-113) + z * ((-132) + z * ((-114) + z * ((-62) + z * ((-73) + z * (13 + z * (53 + z * (12 + z * ((-61) + z * ((-4) + z * ((-1) + z * (1 + z * (81 + z * ((-49) + z * ((-21) + z * (17 + z * ((-37) + z * ((-5) + z * ((-77) + z * ((-37) + z * (59 + z * ((-9) + z * (20 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow9_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_16 z * u8 z = pow9_17_q z * f z + pow9_17 z + (139 : R) * pow9_17_mul_t z := by
  simp only [pow9_16, u8, pow9_17_q, f, pow9_17, pow9_17_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_16 z * u8 z = pow9_17_q z * f z + pow9_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_17_mul_integer z


theorem pow9_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_16 z * u8 z = pow9_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_17_mul z


theorem pow9_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 17 = pow9_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow9_16_pow z hz]
  exact pow9_17_root z hz


def pow9_34 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (102 + z * (62 + z * (20 + z * (37 + z * (26 + z * (51 + z * (71 + z * (124 + z * (4 + z * (113 + z * (89 + z * (34 + z * (60 + z * (138 + z * (113 + z * (54 + z * (118 + z * (69 + z * 124)))))))))))))))))))

def pow9_34_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (117 + z * (4 + z * (25 + z * (60 + z * (20 + z * (79 + z * (128 + z * (107 + z * (134 + z * (64 + z * (16 + z * (125 + z * (125 + z * (48 + z * (55 + z * (64 + z * (123 + z * 83))))))))))))))))))

def pow9_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-73) + z * ((-92) + z * ((-82) + z * ((-151) + z * ((-70) + z * ((-30) + z * ((-196) + z * ((-274) + z * ((-314) + z * ((-342) + z * ((-291) + z * ((-217) + z * ((-298) + z * ((-407) + z * ((-235) + z * ((-325) + z * ((-465) + z * ((-220) + z * ((-286) + z * ((-343) + z * ((-110) + z * ((-208) + z * ((-245) + z * ((-47) + z * ((-83) + z * ((-195) + z * ((-190) + z * (45 + z * (131 + z * ((-55) + z * (6 + z * (33 + z * ((-60) + z * (159 + z * (117 + z * ((-70) + z * (47 + z * 103))))))))))))))))))))))))))))))))))))))

theorem pow9_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_17 z * pow9_17 z = pow9_34_q z * f z + pow9_34 z + (139 : R) * pow9_34_mul_t z := by
  simp only [pow9_17, pow9_34_q, f, pow9_34, pow9_34_mul_t]
  
  ring

theorem pow9_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_17 z * pow9_17 z = pow9_34_q z * f z + pow9_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_34_mul_integer z


theorem pow9_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_17 z * pow9_17 z = pow9_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_34_mul z


theorem pow9_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 34 = pow9_34 z := by
  calc
    _ = u8 z ^ 17 * u8 z ^ 17 := by ring
    _ = pow9_17 z * pow9_17 z := by rw [pow9_17_pow z hz]
    _ = _ := pow9_34_root z hz


def pow9_68 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (128 + z * (101 + z * (7 + z * (104 + z * (29 + z * (95 + z * (37 + z * (71 + z * (20 + z * (0 + z * (44 + z * (16 + z * (123 + z * (92 + z * (65 + z * (133 + z * (55 + z * (30 + z * 8)))))))))))))))))))

def pow9_68_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (5 + z * (129 + z * (101 + z * (62 + z * (125 + z * (64 + z * (120 + z * (117 + z * (74 + z * (20 + z * (114 + z * (28 + z * (36 + z * (105 + z * (41 + z * (101 + z * (127 + z * 86))))))))))))))))))

def pow9_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (110 + z * (177 + z * (82 + z * ((-69) + z * ((-135) + z * ((-248) + z * ((-248) + z * ((-203) + z * ((-108) + z * ((-274) + z * ((-171) + z * ((-223) + z * ((-273) + z * ((-228) + z * ((-72) + z * ((-87) + z * ((-121) + z * ((-235) + z * ((-229) + z * ((-27) + z * ((-225) + z * ((-269) + z * ((-65) + z * ((-98) + z * ((-102) + z * (191 + z * ((-40) + z * (41 + z * (182 + z * (257 + z * (72 + z * (157 + z * (145 + z * (162 + z * (171 + z * (27 + z * (64 + z * (43 + z * 110))))))))))))))))))))))))))))))))))))))

theorem pow9_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_34 z * pow9_34 z = pow9_68_q z * f z + pow9_68 z + (139 : R) * pow9_68_mul_t z := by
  simp only [pow9_34, pow9_68_q, f, pow9_68, pow9_68_mul_t]
  
  ring

theorem pow9_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_34 z * pow9_34 z = pow9_68_q z * f z + pow9_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_68_mul_integer z


theorem pow9_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_34 z * pow9_34 z = pow9_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_68_mul z


theorem pow9_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 68 = pow9_68 z := by
  calc
    _ = u8 z ^ 34 * u8 z ^ 34 := by ring
    _ = pow9_34 z * pow9_34 z := by rw [pow9_34_pow z hz]
    _ = _ := pow9_68_root z hz


def pow9_69 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (64 + z * (125 + z * (82 + z * (16 + z * (100 + z * (42 + z * (46 + z * (76 + z * (58 + z * (18 + z * (81 + z * (57 + z * (127 + z * (130 + z * (132 + z * (22 + z * (121 + z * (96 + z * 22)))))))))))))))))))

def pow9_69_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (30 + z * (82 + z * (1 + z * (1 + z * (24 + z * (85 + z * (80 + z * (102 + z * (63 + z * (104 + z * (68 + z * (63 + z * (58 + z * (118 + z * (127 + z * (72 + z * (37 + z * 116))))))))))))))))))

def pow9_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (84 + z * (46 + z * ((-72) + z * (4 + z * (79 + z * (91 + z * (12 + z * (0 + z * ((-74) + z * ((-149) + z * ((-123) + z * ((-115) + z * ((-41) + z * ((-17) + z * ((-216) + z * ((-202) + z * ((-55) + z * ((-247) + z * ((-297) + z * ((-204) + z * ((-195) + z * ((-160) + z * ((-59) + z * ((-226) + z * ((-150) + z * ((-191) + z * ((-221) + z * ((-226) + z * ((-151) + z * ((-58) + z * ((-128) + z * ((-3) + z * ((-71) + z * ((-126) + z * (31 + z * ((-72) + z * ((-87) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow9_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_68 z * u8 z = pow9_69_q z * f z + pow9_69 z + (139 : R) * pow9_69_mul_t z := by
  simp only [pow9_68, u8, pow9_69_q, f, pow9_69, pow9_69_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_68 z * u8 z = pow9_69_q z * f z + pow9_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_69_mul_integer z


theorem pow9_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_68 z * u8 z = pow9_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_69_mul z


theorem pow9_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 69 = pow9_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow9_68_pow z hz]
  exact pow9_69_root z hz


def pow9_138 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (18 + z * (82 + z * (3 + z * (30 + z * (87 + z * (72 + z * (18 + z * (114 + z * (78 + z * (68 + z * (73 + z * (117 + z * (20 + z * (51 + z * (16 + z * (18 + z * (0 + z * (44 + z * 102)))))))))))))))))))

def pow9_138_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (52 + z * (5 + z * (5 + z * (8 + z * (138 + z * (44 + z * (19 + z * (62 + z * (109 + z * (33 + z * (67 + z * (63 + z * (119 + z * (66 + z * (7 + z * (5 + z * (96 + z * 67))))))))))))))))))

def pow9_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (92 + z * (52 + z * (180 + z * (182 + z * (131 + z * (172 + z * (49 + z * (97 + z * (86 + z * ((-34) + z * (8 + z * (46 + z * ((-44) + z * (98 + z * (119 + z * (188 + z * (252 + z * (332 + z * (184 + z * (193 + z * (232 + z * ((-32) + z * (135 + z * (79 + z * ((-40) + z * (117 + z * (189 + z * (8 + z * (189 + z * (236 + z * (216 + z * (204 + z * (201 + z * (72 + z * (111 + z * (99 + z * ((-33) + z * ((-32) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow9_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_69 z * pow9_69 z = pow9_138_q z * f z + pow9_138 z + (139 : R) * pow9_138_mul_t z := by
  simp only [pow9_69, pow9_138_q, f, pow9_138, pow9_138_mul_t]
  
  ring

theorem pow9_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_69 z * pow9_69 z = pow9_138_q z * f z + pow9_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_138_mul_integer z


theorem pow9_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_69 z * pow9_69 z = pow9_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_138_mul z


theorem pow9_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 138 = pow9_138 z := by
  calc
    _ = u8 z ^ 69 * u8 z ^ 69 := by ring
    _ = pow9_69 z * pow9_69 z := by rw [pow9_69_pow z hz]
    _ = _ := pow9_138_root z hz


def pow9_139 {R : Type*} [CommRing R] (z : R) : R := (94 + z * (83 + z * (71 + z * (34 + z * (63 + z * (64 + z * (52 + z * (63 + z * (11 + z * (126 + z * (79 + z * (8 + z * (46 + z * (113 + z * (77 + z * (134 + z * (121 + z * (128 + z * (31 + z * 60)))))))))))))))))))

def pow9_139_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (100 + z * (45 + z * (110 + z * (6 + z * (105 + z * (79 + z * (11 + z * (33 + z * (129 + z * (17 + z * (41 + z * (33 + z * (48 + z * (92 + z * (2 + z * (119 + z * (81 + z * 89))))))))))))))))))

def pow9_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-82) + z * ((-155) + z * ((-132) + z * ((-235) + z * ((-258) + z * ((-220) + z * ((-162) + z * ((-216) + z * ((-172) + z * ((-218) + z * ((-211) + z * ((-149) + z * ((-84) + z * ((-184) + z * ((-122) + z * ((-192) + z * ((-311) + z * ((-200) + z * ((-298) + z * ((-290) + z * ((-96) + z * ((-112) + z * ((-120) + z * (7 + z * ((-116) + z * ((-58) + z * ((-30) + z * ((-81) + z * (16 + z * ((-2) + z * ((-96) + z * ((-36) + z * ((-180) + z * ((-101) + z * ((-90) + z * ((-58) + z * ((-39) + z * ((-31) + z * 61))))))))))))))))))))))))))))))))))))))

theorem pow9_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_138 z * u8 z = pow9_139_q z * f z + pow9_139 z + (139 : R) * pow9_139_mul_t z := by
  simp only [pow9_138, u8, pow9_139_q, f, pow9_139, pow9_139_mul_t]
  simp only [pow8_139]
  ring

theorem pow9_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow9_138 z * u8 z = pow9_139_q z * f z + pow9_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow9_139_mul_integer z


theorem pow9_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow9_138 z * u8 z = pow9_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_139_mul z


theorem pow9_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u8 z ^ 139 = pow9_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow9_138_pow z hz]
  exact pow9_139_root z hz


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_139 z

theorem iterate9 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 9) = u9 z := by
  calc
    _ = (z ^ (139 ^ 8)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u8 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate8 z hz)
    _ = _ := pow9_139_pow z hz


def pow10_2 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (48 + z * (8 + z * (85 + z * (90 + z * (125 + z * (76 + z * (106 + z * (17 + z * (53 + z * (32 + z * (67 + z * (43 + z * (21 + z * (105 + z * (50 + z * (30 + z * (123 + z * (58 + z * 94)))))))))))))))))))

def pow10_2_q {R : Type*} [CommRing R] (z : R) : R := (52 + z * (97 + z * (71 + z * (44 + z * (106 + z * (107 + z * (33 + z * (26 + z * (4 + z * (64 + z * (64 + z * (138 + z * (122 + z * (97 + z * (98 + z * (82 + z * (124 + z * (91 + z * 125))))))))))))))))))

def pow10_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (24 + z * ((-7) + z * ((-40) + z * ((-102) + z * ((-154) + z * ((-177) + z * ((-140) + z * ((-121) + z * ((-158) + z * ((-45) + z * ((-50) + z * ((-196) + z * ((-313) + z * ((-300) + z * ((-325) + z * ((-230) + z * ((-143) + z * ((-149) + z * ((-241) + z * ((-235) + z * ((-384) + z * ((-273) + z * ((-85) + z * ((-128) + z * ((-132) + z * ((-120) + z * ((-35) + z * ((-181) + z * ((-61) + z * ((-3) + z * ((-20) + z * ((-22) + z * (108 + z * (42 + z * (16 + z * ((-20) + z * ((-59) + z * ((-89) + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow10_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z + (139 : R) * pow10_2_mul_t z := by
  simp only [u9, pow10_2_q, f, pow10_2, pow10_2_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_2_mul_integer z


theorem pow10_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z * u9 z = pow10_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_2_mul z


theorem pow10_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 2 = pow10_2 z := by
  calc
    _ = u9 z ^ 1 * u9 z ^ 1 := by ring
    _ = u9 z * u9 z := by simp only [pow_one]
    _ = _ := pow10_2_root z hz


def pow10_4 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (63 + z * (80 + z * (133 + z * (52 + z * (112 + z * (65 + z * (14 + z * (34 + z * (105 + z * (57 + z * (91 + z * (59 + z * (113 + z * (72 + z * (60 + z * (57 + z * (133 + z * (30 + z * 31)))))))))))))))))))

def pow10_4_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (98 + z * (101 + z * (12 + z * (79 + z * (106 + z * (44 + z * (138 + z * (116 + z * (91 + z * (123 + z * (117 + z * (98 + z * (59 + z * (15 + z * (135 + z * (37 + z * (97 + z * 79))))))))))))))))))

def pow10_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * ((-53) + z * ((-148) + z * ((-139) + z * ((-149) + z * ((-192) + z * ((-128) + z * ((-153) + z * ((-205) + z * ((-256) + z * ((-259) + z * ((-420) + z * ((-364) + z * ((-420) + z * ((-420) + z * ((-481) + z * ((-429) + z * ((-508) + z * ((-432) + z * ((-393) + z * ((-474) + z * ((-305) + z * ((-104) + z * ((-218) + z * ((-168) + z * ((-336) + z * ((-302) + z * ((-362) + z * ((-205) + z * ((-131) + z * ((-178) + z * ((-102) + z * (19 + z * ((-8) + z * ((-16) + z * (37 + z * (43 + z * (5 + z * 63))))))))))))))))))))))))))))))))))))))

theorem pow10_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z + (139 : R) * pow10_4_mul_t z := by
  simp only [pow10_2, pow10_4_q, f, pow10_4, pow10_4_mul_t]
  
  ring

theorem pow10_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_4_mul_integer z


theorem pow10_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_2 z * pow10_2 z = pow10_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_4_mul z


theorem pow10_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 4 = pow10_4 z := by
  calc
    _ = u9 z ^ 2 * u9 z ^ 2 := by ring
    _ = pow10_2 z * pow10_2 z := by rw [pow10_2_pow z hz]
    _ = _ := pow10_4_root z hz


def pow10_8 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (0 + z * (36 + z * (32 + z * (59 + z * (40 + z * (11 + z * (131 + z * (64 + z * (59 + z * (82 + z * (119 + z * (94 + z * (113 + z * (27 + z * (55 + z * (122 + z * (86 + z * (46 + z * 7)))))))))))))))))))

def pow10_8_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (10 + z * (52 + z * (96 + z * (18 + z * (11 + z * (95 + z * (29 + z * (60 + z * (50 + z * (66 + z * (95 + z * (17 + z * (29 + z * (28 + z * (95 + z * (49 + z * (60 + z * 127))))))))))))))))))

def pow10_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-77) + z * ((-76) + z * ((-83) + z * ((-100) + z * ((-51) + z * (49 + z * (47 + z * (5 + z * (41 + z * ((-81) + z * ((-133) + z * ((-37) + z * ((-17) + z * ((-74) + z * (196 + z * (57 + z * (18 + z * (117 + z * ((-13) + z * ((-75) + z * (154 + z * ((-64) + z * (122 + z * (126 + z * ((-47) + z * ((-75) + z * (80 + z * ((-10) + z * (51 + z * (31 + z * (75 + z * ((-30) + z * (40 + z * ((-60) + z * ((-51) + z * ((-7) + z * ((-83) + z * ((-104) + z * 6))))))))))))))))))))))))))))))))))))))

theorem pow10_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z + (139 : R) * pow10_8_mul_t z := by
  simp only [pow10_4, pow10_8_q, f, pow10_8, pow10_8_mul_t]
  
  ring

theorem pow10_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_4 z * pow10_4 z = pow10_8_q z * f z + pow10_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_8_mul_integer z


theorem pow10_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_4 z * pow10_4 z = pow10_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_8_mul z


theorem pow10_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 8 = pow10_8 z := by
  calc
    _ = u9 z ^ 4 * u9 z ^ 4 := by ring
    _ = pow10_4 z * pow10_4 z := by rw [pow10_4_pow z hz]
    _ = _ := pow10_8_root z hz


def pow10_16 {R : Type*} [CommRing R] (z : R) : R := (49 + z * (130 + z * (56 + z * (76 + z * (42 + z * (87 + z * (43 + z * (120 + z * (10 + z * (136 + z * (9 + z * (14 + z * (64 + z * (61 + z * (55 + z * (7 + z * (34 + z * (26 + z * (11 + z * 69)))))))))))))))))))

def pow10_16_q {R : Type*} [CommRing R] (z : R) : R := (73 + z * (45 + z * (47 + z * (74 + z * (112 + z * (136 + z * (26 + z * (85 + z * (22 + z * (76 + z * (106 + z * (9 + z * (44 + z * (134 + z * (25 + z * (17 + z * (76 + z * (71 + z * 49))))))))))))))))))

def pow10_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * ((-99) + z * ((-82) + z * ((-155) + z * ((-186) + z * ((-288) + z * ((-330) + z * ((-182) + z * ((-282) + z * ((-255) + z * ((-276) + z * ((-142) + z * ((-182) + z * ((-301) + z * ((-302) + z * ((-160) + z * ((-117) + z * ((-167) + z * ((-158) + z * ((-233) + z * ((-113) + z * ((-41) + z * ((-54) + z * ((-31) + z * (178 + z * (84 + z * ((-10) + z * (150 + z * (88 + z * (84 + z * (100 + z * ((-63) + z * ((-67) + z * (63 + z * (27 + z * ((-53) + z * ((-78) + z * ((-41) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow10_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z + (139 : R) * pow10_16_mul_t z := by
  simp only [pow10_8, pow10_16_q, f, pow10_16, pow10_16_mul_t]
  
  ring

theorem pow10_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_8 z * pow10_8 z = pow10_16_q z * f z + pow10_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_16_mul_integer z


theorem pow10_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_8 z * pow10_8 z = pow10_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_16_mul z


theorem pow10_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 16 = pow10_16 z := by
  calc
    _ = u9 z ^ 8 * u9 z ^ 8 := by ring
    _ = pow10_8 z * pow10_8 z := by rw [pow10_8_pow z hz]
    _ = _ := pow10_16_root z hz


def pow10_17 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (5 + z * (89 + z * (87 + z * (129 + z * (60 + z * (111 + z * (0 + z * (0 + z * (45 + z * (9 + z * (10 + z * (1 + z * (95 + z * (45 + z * (104 + z * (43 + z * (65 + z * (85 + z * 60)))))))))))))))))))

def pow10_17_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (30 + z * (52 + z * (17 + z * (52 + z * (133 + z * (108 + z * (127 + z * (101 + z * (20 + z * (40 + z * (11 + z * (4 + z * (27 + z * (23 + z * (96 + z * (86 + z * (106 + z * 109))))))))))))))))))

def pow10_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (62 + z * (41 + z * (42 + z * ((-3) + z * ((-28) + z * ((-100) + z * ((-127) + z * ((-253) + z * ((-187) + z * ((-121) + z * ((-110) + z * ((-74) + z * ((-18) + z * (13 + z * ((-159) + z * ((-44) + z * ((-176) + z * ((-176) + z * ((-167) + z * ((-222) + z * ((-209) + z * (2 + z * ((-154) + z * ((-156) + z * ((-211) + z * ((-143) + z * ((-163) + z * ((-14) + z * ((-1) + z * ((-77) + z * ((-128) + z * ((-65) + z * ((-122) + z * ((-132) + z * ((-67) + z * ((-101) + z * ((-81) + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow10_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_16 z * u9 z = pow10_17_q z * f z + pow10_17 z + (139 : R) * pow10_17_mul_t z := by
  simp only [pow10_16, u9, pow10_17_q, f, pow10_17, pow10_17_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_16 z * u9 z = pow10_17_q z * f z + pow10_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_17_mul_integer z


theorem pow10_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_16 z * u9 z = pow10_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_17_mul z


theorem pow10_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 17 = pow10_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow10_16_pow z hz]
  exact pow10_17_root z hz


def pow10_34 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (73 + z * (129 + z * (45 + z * (127 + z * (70 + z * (63 + z * (136 + z * (73 + z * (75 + z * (3 + z * (90 + z * (118 + z * (77 + z * (6 + z * (66 + z * (5 + z * (104 + z * (78 + z * 8)))))))))))))))))))

def pow10_34_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (84 + z * (54 + z * (79 + z * (7 + z * (117 + z * (114 + z * (7 + z * (108 + z * (105 + z * (14 + z * (70 + z * (124 + z * (123 + z * (88 + z * (118 + z * (52 + z * (38 + z * 125))))))))))))))))))

def pow10_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-70) + z * ((-149) + z * ((-171) + z * ((-238) + z * ((-170) + z * ((-170) + z * ((-107) + z * ((-134) + z * ((-115) + z * ((-305) + z * ((-338) + z * ((-384) + z * ((-469) + z * ((-590) + z * ((-665) + z * ((-673) + z * ((-734) + z * ((-377) + z * ((-585) + z * ((-427) + z * ((-326) + z * ((-400) + z * ((-389) + z * ((-281) + z * ((-484) + z * ((-508) + z * ((-383) + z * ((-500) + z * ((-364) + z * ((-212) + z * ((-188) + z * ((-246) + z * ((-51) + z * ((-74) + z * ((-79) + z * (40 + z * ((-19) + z * ((-42) + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow10_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_17 z * pow10_17 z = pow10_34_q z * f z + pow10_34 z + (139 : R) * pow10_34_mul_t z := by
  simp only [pow10_17, pow10_34_q, f, pow10_34, pow10_34_mul_t]
  
  ring

theorem pow10_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_17 z * pow10_17 z = pow10_34_q z * f z + pow10_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_34_mul_integer z


theorem pow10_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_17 z * pow10_17 z = pow10_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_34_mul z


theorem pow10_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 34 = pow10_34 z := by
  calc
    _ = u9 z ^ 17 * u9 z ^ 17 := by ring
    _ = pow10_17 z * pow10_17 z := by rw [pow10_17_pow z hz]
    _ = _ := pow10_34_root z hz


def pow10_68 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (47 + z * (108 + z * (74 + z * (71 + z * (68 + z * (85 + z * (7 + z * (16 + z * (69 + z * (31 + z * (108 + z * (124 + z * (125 + z * (5 + z * (114 + z * (69 + z * (48 + z * (85 + z * 69)))))))))))))))))))

def pow10_68_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (93 + z * (79 + z * (5 + z * (37 + z * (22 + z * (121 + z * (92 + z * (7 + z * (8 + z * (131 + z * (75 + z * (136 + z * (6 + z * (29 + z * (92 + z * (35 + z * (6 + z * 64))))))))))))))))))

def pow10_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-88) + z * ((-113) + z * ((-46) + z * ((-31) + z * (16 + z * (83 + z * ((-9) + z * (89 + z * (145 + z * ((-20) + z * (24 + z * ((-47) + z * (95 + z * (16 + z * ((-41) + z * ((-33) + z * ((-14) + z * (36 + z * (116 + z * ((-56) + z * ((-22) + z * (18 + z * (0 + z * (127 + z * ((-179) + z * ((-65) + z * ((-61) + z * ((-163) + z * (3 + z * (1 + z * ((-178) + z * (27 + z * ((-58) + z * ((-73) + z * (80 + z * (3 + z * ((-50) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow10_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_34 z * pow10_34 z = pow10_68_q z * f z + pow10_68 z + (139 : R) * pow10_68_mul_t z := by
  simp only [pow10_34, pow10_68_q, f, pow10_68, pow10_68_mul_t]
  
  ring

theorem pow10_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_34 z * pow10_34 z = pow10_68_q z * f z + pow10_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_68_mul_integer z


theorem pow10_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_34 z * pow10_34 z = pow10_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_68_mul z


theorem pow10_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 68 = pow10_68 z := by
  calc
    _ = u9 z ^ 34 * u9 z ^ 34 := by ring
    _ = pow10_34 z * pow10_34 z := by rw [pow10_34_pow z hz]
    _ = _ := pow10_68_root z hz


def pow10_69 {R : Type*} [CommRing R] (z : R) : R := (134 + z * (113 + z * (46 + z * (63 + z * (6 + z * (108 + z * (23 + z * (26 + z * (56 + z * (14 + z * (108 + z * (1 + z * (46 + z * (77 + z * (37 + z * (8 + z * (5 + z * (95 + z * (22 + z * 18)))))))))))))))))))

def pow10_69_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (117 + z * (79 + z * (31 + z * (115 + z * (103 + z * (3 + z * (105 + z * (59 + z * (16 + z * (120 + z * (0 + z * (33 + z * (110 + z * (17 + z * (105 + z * (137 + z * (98 + z * 109))))))))))))))))))

def pow10_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-81) + z * ((-99) + z * ((-138) + z * ((-169) + z * ((-175) + z * ((-91) + z * ((-169) + z * ((-281) + z * ((-153) + z * ((-279) + z * ((-215) + z * ((-73) + z * ((-95) + z * ((-221) + z * ((-36) + z * ((-143) + z * ((-208) + z * ((-188) + z * ((-172) + z * ((-313) + z * ((-22) + z * (3 + z * ((-301) + z * ((-30) + z * ((-27) + z * ((-163) + z * (94 + z * (128 + z * (11 + z * (131 + z * ((-59) + z * (33 + z * (8 + z * ((-39) + z * ((-20) + z * ((-68) + z * ((-49) + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow10_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_68 z * u9 z = pow10_69_q z * f z + pow10_69 z + (139 : R) * pow10_69_mul_t z := by
  simp only [pow10_68, u9, pow10_69_q, f, pow10_69, pow10_69_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_68 z * u9 z = pow10_69_q z * f z + pow10_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_69_mul_integer z


theorem pow10_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_68 z * u9 z = pow10_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_69_mul z


theorem pow10_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 69 = pow10_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow10_68_pow z hz]
  exact pow10_69_root z hz


def pow10_138 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (135 + z * (100 + z * (59 + z * (73 + z * (112 + z * (123 + z * (8 + z * (8 + z * (124 + z * (92 + z * (66 + z * (9 + z * (118 + z * (127 + z * (34 + z * (79 + z * (121 + z * (23 + z * 124)))))))))))))))))))

def pow10_138_q {R : Type*} [CommRing R] (z : R) : R := (86 + z * (31 + z * (7 + z * (73 + z * (84 + z * (104 + z * (25 + z * (129 + z * (60 + z * (61 + z * (5 + z * (40 + z * (89 + z * (15 + z * (112 + z * (60 + z * (7 + z * (47 + z * 46))))))))))))))))))

def pow10_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (64 + z * (118 + z * (70 + z * (25 + z * ((-102) + z * ((-16) + z * ((-48) + z * ((-246) + z * ((-172) + z * ((-301) + z * ((-92) + z * ((-159) + z * ((-238) + z * ((-128) + z * ((-317) + z * ((-274) + z * ((-480) + z * ((-280) + z * ((-247) + z * ((-379) + z * ((-271) + z * ((-441) + z * ((-286) + z * ((-335) + z * ((-325) + z * ((-262) + z * ((-239) + z * ((-191) + z * ((-243) + z * ((-71) + z * ((-169) + z * ((-123) + z * ((-109) + z * ((-197) + z * ((-31) + z * ((-10) + z * ((-49) + z * ((-37) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow10_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_69 z * pow10_69 z = pow10_138_q z * f z + pow10_138 z + (139 : R) * pow10_138_mul_t z := by
  simp only [pow10_69, pow10_138_q, f, pow10_138, pow10_138_mul_t]
  
  ring

theorem pow10_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_69 z * pow10_69 z = pow10_138_q z * f z + pow10_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_138_mul_integer z


theorem pow10_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_69 z * pow10_69 z = pow10_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_138_mul z


theorem pow10_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 138 = pow10_138 z := by
  calc
    _ = u9 z ^ 69 * u9 z ^ 69 := by ring
    _ = pow10_69 z * pow10_69 z := by rw [pow10_69_pow z hz]
    _ = _ := pow10_138_root z hz


def pow10_139 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (74 + z * (108 + z * (44 + z * (32 + z * (73 + z * (63 + z * (2 + z * (54 + z * (96 + z * (10 + z * (53 + z * (60 + z * (122 + z * (54 + z * (17 + z * (69 + z * (106 + z * (95 + z * 40)))))))))))))))))))

def pow10_139_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (8 + z * (12 + z * (49 + z * (105 + z * (112 + z * (29 + z * (80 + z * (81 + z * (94 + z * (114 + z * (117 + z * (123 + z * (110 + z * (115 + z * (112 + z * (130 + z * (50 + z * 73))))))))))))))))))

def pow10_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (100 + z * (144 + z * (118 + z * (39 + z * (9 + z * (46 + z * ((-42) + z * ((-110) + z * ((-80) + z * ((-3) + z * ((-91) + z * ((-302) + z * ((-312) + z * ((-235) + z * ((-168) + z * ((-219) + z * ((-256) + z * ((-141) + z * ((-63) + z * ((-162) + z * ((-166) + z * ((-169) + z * ((-197) + z * ((-245) + z * ((-237) + z * ((-101) + z * ((-176) + z * ((-98) + z * ((-71) + z * ((-46) + z * ((-81) + z * (52 + z * (54 + z * (23 + z * (33 + z * (71 + z * ((-30) + z * 53))))))))))))))))))))))))))))))))))))))

theorem pow10_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_138 z * u9 z = pow10_139_q z * f z + pow10_139 z + (139 : R) * pow10_139_mul_t z := by
  simp only [pow10_138, u9, pow10_139_q, f, pow10_139, pow10_139_mul_t]
  simp only [pow9_139]
  ring

theorem pow10_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow10_138 z * u9 z = pow10_139_q z * f z + pow10_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow10_139_mul_integer z


theorem pow10_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow10_138 z * u9 z = pow10_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_139_mul z


theorem pow10_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u9 z ^ 139 = pow10_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow10_138_pow z hz]
  exact pow10_139_root z hz


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_139 z

theorem iterate10 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 10) = u10 z := by
  calc
    _ = (z ^ (139 ^ 9)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u9 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate9 z hz)
    _ = _ := pow10_139_pow z hz

end DimensionTen.Mod139

end

end OAI
