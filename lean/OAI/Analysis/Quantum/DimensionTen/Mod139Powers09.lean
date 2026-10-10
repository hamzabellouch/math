import OAI.Analysis.Quantum.DimensionTen.Mod139Powers08

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow17_2 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (110 + z * (129 + z * (19 + z * (43 + z * (94 + z * (94 + z * (24 + z * (8 + z * (41 + z * (86 + z * (62 + z * (67 + z * (116 + z * (119 + z * (81 + z * (80 + z * (50 + z * (11 + z * 130)))))))))))))))))))

def pow17_2_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (63 + z * (84 + z * (38 + z * (106 + z * (96 + z * (75 + z * (99 + z * (61 + z * (66 + z * (126 + z * (72 + z * (60 + z * (55 + z * (29 + z * (105 + z * (136 + z * (130 + z * 11))))))))))))))))))

def pow17_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-84) + z * ((-105) + z * ((-126) + z * ((-140) + z * ((-160) + z * ((-91) + z * ((-108) + z * ((-172) + z * ((-192) + z * ((-207) + z * ((-333) + z * ((-272) + z * ((-166) + z * ((-410) + z * ((-272) + z * ((-204) + z * ((-332) + z * ((-318) + z * ((-348) + z * ((-364) + z * ((-309) + z * ((-7) + z * ((-190) + z * ((-190) + z * ((-76) + z * ((-380) + z * ((-145) + z * ((-92) + z * ((-135) + z * ((-74) + z * ((-19) + z * ((-92) + z * ((-54) + z * (60 + z * ((-71) + z * ((-7) + z * ((-54) + z * (10 + z * 107))))))))))))))))))))))))))))))))))))))

theorem pow17_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z + (139 : R) * pow17_2_mul_t z := by
  simp only [u16, pow17_2_q, f, pow17_2, pow17_2_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_2_mul_integer z


theorem pow17_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z * u16 z = pow17_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_2_mul z


theorem pow17_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 2 = pow17_2 z := by
  calc
    _ = u16 z ^ 1 * u16 z ^ 1 := by ring
    _ = u16 z * u16 z := by simp only [pow_one]
    _ = _ := pow17_2_root z hz


def pow17_4 {R : Type*} [CommRing R] (z : R) : R := (89 + z * (44 + z * (66 + z * (56 + z * (10 + z * (46 + z * (99 + z * (58 + z * (92 + z * (46 + z * (53 + z * (95 + z * (116 + z * (26 + z * (84 + z * (78 + z * (37 + z * (63 + z * (7 + z * 59)))))))))))))))))))

def pow17_4_q {R : Type*} [CommRing R] (z : R) : R := (68 + z * (108 + z * (137 + z * (65 + z * (130 + z * (84 + z * (78 + z * (28 + z * (55 + z * (137 + z * (97 + z * (25 + z * (117 + z * (37 + z * (135 + z * (112 + z * (111 + z * (137 + z * 81))))))))))))))))))

def pow17_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-52) + z * ((-140) + z * ((-171) + z * ((-127) + z * ((-284) + z * ((-367) + z * ((-243) + z * ((-121) + z * ((-232) + z * ((-432) + z * ((-464) + z * ((-344) + z * ((-386) + z * ((-450) + z * ((-386) + z * ((-265) + z * ((-335) + z * ((-482) + z * ((-534) + z * ((-561) + z * ((-341) + z * ((-226) + z * ((-408) + z * ((-295) + z * ((-216) + z * ((-204) + z * ((-118) + z * ((-213) + z * ((-168) + z * (63 + z * ((-94) + z * ((-110) + z * ((-8) + z * ((-80) + z * ((-71) + z * ((-46) + z * ((-92) + z * ((-55) + z * 121))))))))))))))))))))))))))))))))))))))

theorem pow17_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z + (139 : R) * pow17_4_mul_t z := by
  simp only [pow17_2, pow17_4_q, f, pow17_4, pow17_4_mul_t]
  
  ring

theorem pow17_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_4_mul_integer z


theorem pow17_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_2 z * pow17_2 z = pow17_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_4_mul z


theorem pow17_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 4 = pow17_4 z := by
  calc
    _ = u16 z ^ 2 * u16 z ^ 2 := by ring
    _ = pow17_2 z * pow17_2 z := by rw [pow17_2_pow z hz]
    _ = _ := pow17_4_root z hz


def pow17_8 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (47 + z * (8 + z * (123 + z * (82 + z * (71 + z * (104 + z * (28 + z * (133 + z * (66 + z * (8 + z * (100 + z * (19 + z * (136 + z * (71 + z * (44 + z * (27 + z * (118 + z * (33 + z * 28)))))))))))))))))))

def pow17_8_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (22 + z * (108 + z * (7 + z * (33 + z * (60 + z * (122 + z * (116 + z * (63 + z * (99 + z * (27 + z * (95 + z * (52 + z * (115 + z * (5 + z * (60 + z * (3 + z * (58 + z * 6))))))))))))))))))

def pow17_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (53 + z * (35 + z * ((-7) + z * ((-12) + z * ((-74) + z * ((-84) + z * ((-87) + z * ((-140) + z * ((-111) + z * ((-228) + z * ((-227) + z * ((-184) + z * ((-119) + z * ((-162) + z * ((-78) + z * ((-243) + z * ((-196) + z * ((-79) + z * ((-104) + z * ((-49) + z * ((-116) + z * ((-188) + z * ((-73) + z * ((-16) + z * ((-93) + z * ((-97) + z * ((-57) + z * ((-31) + z * ((-34) + z * (30 + z * ((-21) + z * (4 + z * ((-41) + z * (11 + z * (36 + z * ((-8) + z * ((-4) + z * (0 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow17_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z + (139 : R) * pow17_8_mul_t z := by
  simp only [pow17_4, pow17_8_q, f, pow17_8, pow17_8_mul_t]
  
  ring

theorem pow17_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_8_mul_integer z


theorem pow17_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_4 z * pow17_4 z = pow17_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_8_mul z


theorem pow17_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 8 = pow17_8 z := by
  calc
    _ = u16 z ^ 4 * u16 z ^ 4 := by ring
    _ = pow17_4 z * pow17_4 z := by rw [pow17_4_pow z hz]
    _ = _ := pow17_8_root z hz


def pow17_16 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (103 + z * (91 + z * (7 + z * (111 + z * (100 + z * (0 + z * (17 + z * (119 + z * (89 + z * (22 + z * (71 + z * (107 + z * (107 + z * (111 + z * (6 + z * (41 + z * (69 + z * (91 + z * 16)))))))))))))))))))

def pow17_16_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (100 + z * (107 + z * (19 + z * (124 + z * (47 + z * (121 + z * (108 + z * (126 + z * (105 + z * (126 + z * (138 + z * (3 + z * (2 + z * (130 + z * (6 + z * (109 + z * (47 + z * 89))))))))))))))))))

def pow17_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-83) + z * ((-177) + z * ((-170) + z * ((-208) + z * ((-252) + z * ((-177) + z * ((-211) + z * ((-296) + z * ((-236) + z * ((-469) + z * ((-413) + z * ((-300) + z * ((-350) + z * ((-252) + z * ((-385) + z * ((-246) + z * ((-310) + z * ((-437) + z * ((-312) + z * ((-410) + z * ((-201) + z * ((-88) + z * ((-287) + z * ((-313) + z * ((-173) + z * ((-214) + z * ((-293) + z * ((-48) + z * ((-258) + z * ((-32) + z * (27 + z * ((-87) + z * ((-125) + z * ((-30) + z * ((-68) + z * ((-54) + z * ((-69) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow17_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z + (139 : R) * pow17_16_mul_t z := by
  simp only [pow17_8, pow17_16_q, f, pow17_16, pow17_16_mul_t]
  
  ring

theorem pow17_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_16_mul_integer z


theorem pow17_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_8 z * pow17_8 z = pow17_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_16_mul z


theorem pow17_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 16 = pow17_16 z := by
  calc
    _ = u16 z ^ 8 * u16 z ^ 8 := by ring
    _ = pow17_8 z * pow17_8 z := by rw [pow17_8_pow z hz]
    _ = _ := pow17_16_root z hz


def pow17_17 {R : Type*} [CommRing R] (z : R) : R := (127 + z * (70 + z * (108 + z * (19 + z * (94 + z * (15 + z * (22 + z * (27 + z * (99 + z * (84 + z * (135 + z * (6 + z * (88 + z * (125 + z * (112 + z * (80 + z * (21 + z * (63 + z * (5 + z * 37)))))))))))))))))))

def pow17_17_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (130 + z * (36 + z * (28 + z * (67 + z * (129 + z * (119 + z * (126 + z * (63 + z * (97 + z * (13 + z * (89 + z * (33 + z * (113 + z * (75 + z * (23 + z * (117 + z * (101 + z * 6))))))))))))))))))

def pow17_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * ((-30) + z * ((-14) + z * ((-27) + z * ((-52) + z * ((-52) + z * ((-70) + z * ((-219) + z * ((-259) + z * ((-187) + z * ((-254) + z * ((-261) + z * ((-59) + z * ((-142) + z * ((-278) + z * ((-165) + z * ((-202) + z * ((-351) + z * ((-105) + z * ((-161) + z * ((-293) + z * ((-127) + z * ((-174) + z * ((-135) + z * ((-149) + z * ((-192) + z * ((-245) + z * ((-48) + z * (132 + z * ((-79) + z * ((-42) + z * ((-12) + z * ((-77) + z * (45 + z * (1 + z * ((-99) + z * ((-25) + z * (75 + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow17_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_16 z * u16 z = pow17_17_q z * f z + pow17_17 z + (139 : R) * pow17_17_mul_t z := by
  simp only [pow17_16, u16, pow17_17_q, f, pow17_17, pow17_17_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_16 z * u16 z = pow17_17_q z * f z + pow17_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_17_mul_integer z


theorem pow17_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_16 z * u16 z = pow17_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_17_mul z


theorem pow17_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 17 = pow17_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow17_16_pow z hz]
  exact pow17_17_root z hz


def pow17_34 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (80 + z * (23 + z * (132 + z * (110 + z * (4 + z * (72 + z * (130 + z * (87 + z * (91 + z * (58 + z * (68 + z * (30 + z * (114 + z * (21 + z * (16 + z * (34 + z * (100 + z * (103 + z * 59)))))))))))))))))))

def pow17_34_q {R : Type*} [CommRing R] (z : R) : R := (90 + z * (64 + z * (15 + z * (113 + z * (94 + z * (62 + z * (4 + z * (127 + z * (27 + z * (54 + z * (0 + z * (25 + z * (26 + z * (20 + z * (66 + z * (19 + z * (18 + z * (0 + z * 118))))))))))))))))))

def pow17_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (48 + z * (0 + z * (84 + z * ((-99) + z * ((-41) + z * ((-171) + z * ((-108) + z * ((-290) + z * ((-84) + z * ((-99) + z * (63 + z * ((-81) + z * (154 + z * (20 + z * (222 + z * (129 + z * (34 + z * (133 + z * (24 + z * ((-41) + z * ((-68) + z * (52 + z * (36 + z * (156 + z * (161 + z * (156 + z * (113 + z * (203 + z * (71 + z * (190 + z * (57 + z * (5 + z * (19 + z * ((-66) + z * ((-57) + z * ((-1) + z * ((-53) + z * ((-106) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow17_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_17 z * pow17_17 z = pow17_34_q z * f z + pow17_34 z + (139 : R) * pow17_34_mul_t z := by
  simp only [pow17_17, pow17_34_q, f, pow17_34, pow17_34_mul_t]
  
  ring

theorem pow17_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_17 z * pow17_17 z = pow17_34_q z * f z + pow17_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_34_mul_integer z


theorem pow17_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_17 z * pow17_17 z = pow17_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_34_mul z


theorem pow17_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 34 = pow17_34 z := by
  calc
    _ = u16 z ^ 17 * u16 z ^ 17 := by ring
    _ = pow17_17 z * pow17_17 z := by rw [pow17_17_pow z hz]
    _ = _ := pow17_34_root z hz


def pow17_68 {R : Type*} [CommRing R] (z : R) : R := (99 + z * (47 + z * (67 + z * (45 + z * (15 + z * (1 + z * (76 + z * (18 + z * (88 + z * (40 + z * (18 + z * (35 + z * (17 + z * (107 + z * (41 + z * (87 + z * (29 + z * (35 + z * (36 + z * 19)))))))))))))))))))

def pow17_68_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (74 + z * (55 + z * (127 + z * (24 + z * (11 + z * (1 + z * (113 + z * (37 + z * (110 + z * (83 + z * (73 + z * (53 + z * (131 + z * (123 + z * (51 + z * (120 + z * (127 + z * 6))))))))))))))))))

def pow17_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-71) + z * ((-82) + z * ((-196) + z * ((-103) + z * ((-91) + z * ((-54) + z * (31 + z * (6 + z * ((-77) + z * ((-2) + z * ((-86) + z * ((-96) + z * ((-171) + z * ((-73) + z * ((-178) + z * ((-280) + z * ((-364) + z * ((-339) + z * ((-262) + z * ((-67) + z * ((-29) + z * ((-129) + z * ((-238) + z * ((-65) + z * ((-89) + z * ((-146) + z * ((-182) + z * ((-148) + z * ((-231) + z * ((-134) + z * ((-91) + z * ((-236) + z * ((-171) + z * ((-5) + z * ((-27) + z * (39 + z * (81 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow17_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_34 z * pow17_34 z = pow17_68_q z * f z + pow17_68 z + (139 : R) * pow17_68_mul_t z := by
  simp only [pow17_34, pow17_68_q, f, pow17_68, pow17_68_mul_t]
  
  ring

theorem pow17_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_34 z * pow17_34 z = pow17_68_q z * f z + pow17_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_68_mul_integer z


theorem pow17_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_34 z * pow17_34 z = pow17_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_68_mul z


theorem pow17_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 68 = pow17_68 z := by
  calc
    _ = u16 z ^ 34 * u16 z ^ 34 := by ring
    _ = pow17_34 z * pow17_34 z := by rw [pow17_34_pow z hz]
    _ = _ := pow17_68_root z hz


def pow17_69 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (118 + z * (94 + z * (26 + z * (88 + z * (112 + z * (127 + z * (30 + z * (28 + z * (31 + z * (74 + z * (41 + z * (48 + z * (88 + z * (118 + z * (121 + z * (137 + z * (74 + z * (114 + z * 20)))))))))))))))))))

def pow17_69_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (34 + z * (52 + z * (18 + z * (12 + z * (89 + z * (8 + z * (5 + z * (23 + z * (109 + z * (76 + z * (11 + z * (0 + z * (56 + z * (79 + z * (114 + z * (4 + z * (94 + z * 94))))))))))))))))))

def pow17_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-30) + z * ((-39) + z * ((-51) + z * ((-13) + z * ((-15) + z * ((-50) + z * (29 + z * ((-8) + z * ((-115) + z * ((-94) + z * ((-66) + z * ((-110) + z * ((-62) + z * ((-64) + z * ((-142) + z * ((-37) + z * ((-110) + z * ((-272) + z * ((-223) + z * ((-95) + z * ((-167) + z * ((-38) + z * ((-142) + z * ((-212) + z * ((-82) + z * ((-112) + z * ((-112) + z * ((-229) + z * ((-20) + z * ((-74) + z * ((-100) + z * ((-15) + z * ((-183) + z * ((-59) + z * ((-18) + z * ((-116) + z * ((-54) + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow17_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_68 z * u16 z = pow17_69_q z * f z + pow17_69 z + (139 : R) * pow17_69_mul_t z := by
  simp only [pow17_68, u16, pow17_69_q, f, pow17_69, pow17_69_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_68 z * u16 z = pow17_69_q z * f z + pow17_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_69_mul_integer z


theorem pow17_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_68 z * u16 z = pow17_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_69_mul z


theorem pow17_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 69 = pow17_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow17_68_pow z hz]
  exact pow17_69_root z hz


def pow17_138 {R : Type*} [CommRing R] (z : R) : R := (118 + z * (118 + z * (66 + z * (127 + z * (4 + z * (82 + z * (46 + z * (125 + z * (107 + z * (49 + z * (91 + z * (27 + z * (100 + z * (24 + z * (12 + z * (91 + z * (14 + z * (17 + z * (138 + z * 92)))))))))))))))))))

def pow17_138_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (88 + z * (41 + z * (85 + z * (31 + z * (105 + z * (62 + z * (71 + z * (54 + z * (110 + z * (119 + z * (7 + z * (126 + z * (135 + z * (93 + z * (67 + z * (46 + z * (64 + z * 122))))))))))))))))))

def pow17_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-72) + z * ((-86) + z * ((-47) + z * ((-114) + z * ((-140) + z * ((-62) + z * (58 + z * (14 + z * ((-98) + z * ((-248) + z * ((-249) + z * ((-133) + z * ((-220) + z * ((-436) + z * ((-293) + z * ((-193) + z * ((-165) + z * ((-29) + z * ((-75) + z * ((-81) + z * (53 + z * ((-50) + z * ((-90) + z * ((-94) + z * ((-51) + z * ((-225) + z * ((-152) + z * ((-103) + z * ((-105) + z * (117 + z * (193 + z * (81 + z * (159 + z * (111 + z * (101 + z * (71 + z * ((-34) + z * ((-80) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow17_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_69 z * pow17_69 z = pow17_138_q z * f z + pow17_138 z + (139 : R) * pow17_138_mul_t z := by
  simp only [pow17_69, pow17_138_q, f, pow17_138, pow17_138_mul_t]
  
  ring

theorem pow17_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_69 z * pow17_69 z = pow17_138_q z * f z + pow17_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_138_mul_integer z


theorem pow17_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_69 z * pow17_69 z = pow17_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_138_mul z


theorem pow17_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 138 = pow17_138 z := by
  calc
    _ = u16 z ^ 69 * u16 z ^ 69 := by ring
    _ = pow17_69 z * pow17_69 z := by rw [pow17_69_pow z hz]
    _ = _ := pow17_138_root z hz


def pow17_139 {R : Type*} [CommRing R] (z : R) : R := (63 + z * (5 + z * (33 + z * (67 + z * (66 + z * (39 + z * (107 + z * (38 + z * (87 + z * (81 + z * (59 + z * (19 + z * (136 + z * (42 + z * (111 + z * (137 + z * (13 + z * (98 + z * (16 + z * 127)))))))))))))))))))

def pow17_139_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (78 + z * (63 + z * (48 + z * (30 + z * (122 + z * (109 + z * (6 + z * (28 + z * (100 + z * (33 + z * (95 + z * (75 + z * (108 + z * (107 + z * (89 + z * (78 + z * (41 + z * 104))))))))))))))))))

def pow17_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (17 + z * (13 + z * (3 + z * (22 + z * (27 + z * ((-78) + z * (16 + z * (50 + z * ((-96) + z * (53 + z * ((-13) + z * ((-8) + z * ((-126) + z * ((-182) + z * ((-237) + z * ((-233) + z * ((-51) + z * ((-341) + z * ((-129) + z * ((-106) + z * ((-249) + z * ((-28) + z * ((-48) + z * ((-239) + z * ((-204) + z * (22 + z * ((-229) + z * ((-194) + z * ((-50) + z * ((-197) + z * ((-134) + z * ((-108) + z * ((-96) + z * (15 + z * (31 + z * ((-60) + z * (33 + z * 80))))))))))))))))))))))))))))))))))))))

theorem pow17_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_138 z * u16 z = pow17_139_q z * f z + pow17_139 z + (139 : R) * pow17_139_mul_t z := by
  simp only [pow17_138, u16, pow17_139_q, f, pow17_139, pow17_139_mul_t]
  simp only [pow16_139]
  ring

theorem pow17_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow17_138 z * u16 z = pow17_139_q z * f z + pow17_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow17_139_mul_integer z


theorem pow17_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow17_138 z * u16 z = pow17_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_139_mul z


theorem pow17_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u16 z ^ 139 = pow17_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow17_138_pow z hz]
  exact pow17_139_root z hz


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_139 z

theorem iterate17 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 17) = u17 z := by
  calc
    _ = (z ^ (139 ^ 16)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate16 z hz)
    _ = _ := pow17_139_pow z hz


def pow18_2 {R : Type*} [CommRing R] (z : R) : R := (93 + z * (115 + z * (7 + z * (121 + z * (89 + z * (36 + z * (73 + z * (35 + z * (138 + z * (122 + z * (55 + z * (40 + z * (90 + z * (72 + z * (52 + z * (5 + z * (116 + z * (97 + z * (6 + z * 104)))))))))))))))))))

def pow18_2_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (95 + z * (126 + z * (88 + z * (88 + z * (14 + z * (50 + z * (48 + z * (36 + z * (60 + z * (87 + z * (98 + z * (69 + z * (131 + z * (71 + z * (16 + z * (30 + z * (88 + z * 5))))))))))))))))))

def pow18_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * ((-90) + z * ((-171) + z * ((-224) + z * ((-295) + z * ((-297) + z * ((-186) + z * ((-206) + z * ((-133) + z * ((-143) + z * ((-246) + z * ((-361) + z * ((-200) + z * ((-379) + z * ((-293) + z * ((-193) + z * ((-280) + z * ((-245) + z * ((-55) + z * ((-114) + z * ((-160) + z * (6 + z * ((-9) + z * (114 + z * (121 + z * (137 + z * ((-4) + z * (174 + z * (48 + z * (166 + z * ((-26) + z * (206 + z * (40 + z * (98 + z * (281 + z * ((-46) + z * (96 + z * (24 + z * 116))))))))))))))))))))))))))))))))))))))

theorem pow18_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z + (139 : R) * pow18_2_mul_t z := by
  simp only [u17, pow18_2_q, f, pow18_2, pow18_2_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_2_mul_integer z


theorem pow18_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z * u17 z = pow18_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_2_mul z


theorem pow18_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 2 = pow18_2 z := by
  calc
    _ = u17 z ^ 1 * u17 z ^ 1 := by ring
    _ = u17 z * u17 z := by simp only [pow_one]
    _ = _ := pow18_2_root z hz


def pow18_4 {R : Type*} [CommRing R] (z : R) : R := (42 + z * (42 + z * (88 + z * (21 + z * (89 + z * (91 + z * (123 + z * (114 + z * (28 + z * (81 + z * (87 + z * (117 + z * (81 + z * (89 + z * (43 + z * (82 + z * (9 + z * (21 + z * (17 + z * 60)))))))))))))))))))

def pow18_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (69 + z * (32 + z * (118 + z * (90 + z * (9 + z * (119 + z * (118 + z * (90 + z * (27 + z * (86 + z * (124 + z * (91 + z * (52 + z * (133 + z * (116 + z * (86 + z * (128 + z * 113))))))))))))))))))

def pow18_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (33 + z * ((-51) + z * ((-80) + z * ((-8) + z * ((-93) + z * ((-93) + z * ((-131) + z * ((-117) + z * (51 + z * ((-175) + z * ((-160) + z * ((-13) + z * ((-153) + z * ((-257) + z * ((-321) + z * ((-328) + z * ((-146) + z * ((-402) + z * ((-417) + z * ((-144) + z * ((-366) + z * ((-215) + z * ((-238) + z * ((-273) + z * ((-139) + z * ((-295) + z * ((-260) + z * ((-104) + z * ((-149) + z * ((-295) + z * ((-212) + z * ((-131) + z * ((-147) + z * ((-180) + z * (8 + z * ((-56) + z * ((-96) + z * 77))))))))))))))))))))))))))))))))))))))

theorem pow18_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z + (139 : R) * pow18_4_mul_t z := by
  simp only [pow18_2, pow18_4_q, f, pow18_4, pow18_4_mul_t]
  
  ring

theorem pow18_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_4_mul_integer z


theorem pow18_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_2 z * pow18_2 z = pow18_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_4_mul z


theorem pow18_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 4 = pow18_4 z := by
  calc
    _ = u17 z ^ 2 * u17 z ^ 2 := by ring
    _ = pow18_2 z * pow18_2 z := by rw [pow18_2_pow z hz]
    _ = _ := pow18_4_root z hz


def pow18_8 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (85 + z * (18 + z * (78 + z * (88 + z * (114 + z * (67 + z * (76 + z * (22 + z * (10 + z * (10 + z * (68 + z * (1 + z * (34 + z * (6 + z * (108 + z * (42 + z * (60 + z * (69 + z * 49)))))))))))))))))))

def pow18_8_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (43 + z * (76 + z * (26 + z * (14 + z * (1 + z * (69 + z * (61 + z * (108 + z * (39 + z * (19 + z * (29 + z * (79 + z * (10 + z * (11 + z * (1 + z * (102 + z * (79 + z * 125))))))))))))))))))

def pow18_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * ((-20) + z * ((-42) + z * ((-73) + z * ((-32) + z * ((-12) + z * (77 + z * (98 + z * (51 + z * (27 + z * (18 + z * (163 + z * (164 + z * (297 + z * (241 + z * (267 + z * (210 + z * (226 + z * (59 + z * (97 + z * (35 + z * (18 + z * (65 + z * (148 + z * (114 + z * ((-14) + z * ((-67) + z * ((-189) + z * ((-38) + z * ((-7) + z * ((-40) + z * ((-181) + z * ((-93) + z * ((-97) + z * ((-104) + z * ((-139) + z * ((-145) + z * ((-101) + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow18_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_4 z * pow18_4 z = pow18_8_q z * f z + pow18_8 z + (139 : R) * pow18_8_mul_t z := by
  simp only [pow18_4, pow18_8_q, f, pow18_8, pow18_8_mul_t]
  
  ring

theorem pow18_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_4 z * pow18_4 z = pow18_8_q z * f z + pow18_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_8_mul_integer z


theorem pow18_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_4 z * pow18_4 z = pow18_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_8_mul z


theorem pow18_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 8 = pow18_8 z := by
  calc
    _ = u17 z ^ 4 * u17 z ^ 4 := by ring
    _ = pow18_4 z * pow18_4 z := by rw [pow18_4_pow z hz]
    _ = _ := pow18_8_root z hz


def pow18_16 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (55 + z * (17 + z * (131 + z * (111 + z * (21 + z * (55 + z * (69 + z * (0 + z * (77 + z * (99 + z * (19 + z * (115 + z * (56 + z * (129 + z * (122 + z * (25 + z * (82 + z * (75 + z * 41)))))))))))))))))))

def pow18_16_q {R : Type*} [CommRing R] (z : R) : R := (68 + z * (137 + z * (112 + z * (37 + z * (59 + z * (51 + z * (19 + z * (107 + z * (31 + z * (124 + z * (41 + z * (125 + z * (111 + z * (89 + z * (0 + z * (136 + z * (121 + z * (91 + z * 38))))))))))))))))))

def pow18_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-50) + z * ((-144) + z * ((-210) + z * ((-275) + z * ((-244) + z * ((-204) + z * ((-79) + z * ((-120) + z * ((-94) + z * ((-235) + z * ((-304) + z * ((-416) + z * ((-380) + z * ((-548) + z * ((-530) + z * ((-635) + z * ((-564) + z * ((-717) + z * ((-545) + z * ((-598) + z * ((-520) + z * ((-391) + z * ((-249) + z * ((-300) + z * ((-320) + z * ((-543) + z * ((-409) + z * ((-435) + z * ((-379) + z * ((-300) + z * ((-263) + z * ((-328) + z * ((-122) + z * ((-53) + z * ((-102) + z * ((-90) + z * ((-36) + z * (13 + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow18_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_8 z * pow18_8 z = pow18_16_q z * f z + pow18_16 z + (139 : R) * pow18_16_mul_t z := by
  simp only [pow18_8, pow18_16_q, f, pow18_16, pow18_16_mul_t]
  
  ring

theorem pow18_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_8 z * pow18_8 z = pow18_16_q z * f z + pow18_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_16_mul_integer z


theorem pow18_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_8 z * pow18_8 z = pow18_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_16_mul z


theorem pow18_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 16 = pow18_16 z := by
  calc
    _ = u17 z ^ 8 * u17 z ^ 8 := by ring
    _ = pow18_8 z * pow18_8 z := by rw [pow18_8_pow z hz]
    _ = _ := pow18_16_root z hz


def pow18_17 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (55 + z * (36 + z * (114 + z * (77 + z * (69 + z * (7 + z * (86 + z * (135 + z * (19 + z * (56 + z * (98 + z * (111 + z * (60 + z * (93 + z * (124 + z * (73 + z * (82 + z * (98 + z * 31)))))))))))))))))))

def pow18_17_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (69 + z * (88 + z * (87 + z * (12 + z * (124 + z * (86 + z * (95 + z * (128 + z * (58 + z * (58 + z * (60 + z * (34 + z * (27 + z * (12 + z * (46 + z * (125 + z * (43 + z * 64))))))))))))))))))

def pow18_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-77) + z * ((-155) + z * ((-157) + z * ((-160) + z * ((-241) + z * ((-188) + z * ((-203) + z * ((-329) + z * ((-295) + z * ((-319) + z * ((-376) + z * ((-205) + z * ((-185) + z * ((-195) + z * ((-113) + z * ((-229) + z * ((-184) + z * ((-134) + z * ((-166) + z * ((-148) + z * ((-108) + z * (84 + z * (30 + z * (5 + z * ((-58) + z * ((-3) + z * (113 + z * (99 + z * (230 + z * (98 + z * (119 + z * (115 + z * (142 + z * (32 + z * ((-58) + z * (25 + z * (14 + z * 37))))))))))))))))))))))))))))))))))))))

theorem pow18_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_16 z * u17 z = pow18_17_q z * f z + pow18_17 z + (139 : R) * pow18_17_mul_t z := by
  simp only [pow18_16, u17, pow18_17_q, f, pow18_17, pow18_17_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_16 z * u17 z = pow18_17_q z * f z + pow18_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_17_mul_integer z


theorem pow18_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_16 z * u17 z = pow18_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_17_mul z


theorem pow18_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 17 = pow18_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow18_16_pow z hz]
  exact pow18_17_root z hz


def pow18_34 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (103 + z * (123 + z * (124 + z * (17 + z * (10 + z * (9 + z * (34 + z * (15 + z * (74 + z * (8 + z * (115 + z * (54 + z * (4 + z * (22 + z * (28 + z * (41 + z * (71 + z * (98 + z * 68)))))))))))))))))))

def pow18_34_q {R : Type*} [CommRing R] (z : R) : R := (117 + z * (10 + z * (46 + z * (66 + z * (57 + z * (11 + z * (124 + z * (131 + z * (45 + z * (82 + z * (122 + z * (3 + z * (131 + z * (14 + z * (65 + z * (125 + z * (120 + z * (106 + z * 127))))))))))))))))))

def pow18_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-72) + z * ((-73) + z * ((-103) + z * ((-104) + z * ((-91) + z * ((-37) + z * ((-104) + z * ((-179) + z * ((-102) + z * ((-265) + z * ((-328) + z * ((-69) + z * ((-128) + z * ((-242) + z * ((-132) + z * ((-17) + z * ((-248) + z * ((-217) + z * ((-181) + z * ((-232) + z * ((-112) + z * ((-72) + z * ((-78) + z * (43 + z * ((-55) + z * ((-223) + z * (10 + z * (9 + z * ((-116) + z * (136 + z * (65 + z * ((-101) + z * (60 + z * ((-19) + z * ((-103) + z * ((-41) + z * ((-86) + z * ((-74) + z * 6))))))))))))))))))))))))))))))))))))))

theorem pow18_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_17 z * pow18_17 z = pow18_34_q z * f z + pow18_34 z + (139 : R) * pow18_34_mul_t z := by
  simp only [pow18_17, pow18_34_q, f, pow18_34, pow18_34_mul_t]
  
  ring

theorem pow18_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_17 z * pow18_17 z = pow18_34_q z * f z + pow18_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_34_mul_integer z


theorem pow18_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_17 z * pow18_17 z = pow18_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_34_mul z


theorem pow18_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 34 = pow18_34 z := by
  calc
    _ = u17 z ^ 17 * u17 z ^ 17 := by ring
    _ = pow18_17 z * pow18_17 z := by rw [pow18_17_pow z hz]
    _ = _ := pow18_34_root z hz


def pow18_68 {R : Type*} [CommRing R] (z : R) : R := (94 + z * (113 + z * (71 + z * (5 + z * (98 + z * (131 + z * (135 + z * (108 + z * (90 + z * (120 + z * (5 + z * (65 + z * (86 + z * (108 + z * (53 + z * (73 + z * (133 + z * (88 + z * (23 + z * 137)))))))))))))))))))

def pow18_68_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (31 + z * (15 + z * (19 + z * (26 + z * (56 + z * (41 + z * (82 + z * (103 + z * (77 + z * (6 + z * (75 + z * (32 + z * (69 + z * (97 + z * (26 + z * (49 + z * (113 + z * 37))))))))))))))))))

def pow18_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-40) + z * ((-36) + z * (32 + z * (119 + z * (173 + z * (109 + z * ((-5) + z * ((-162) + z * ((-230) + z * ((-267) + z * ((-201) + z * ((-183) + z * ((-40) + z * ((-111) + z * ((-163) + z * ((-360) + z * ((-414) + z * ((-419) + z * ((-299) + z * ((-169) + z * ((-26) + z * ((-188) + z * ((-211) + z * ((-326) + z * ((-407) + z * ((-259) + z * ((-279) + z * ((-296) + z * ((-47) + z * ((-37) + z * ((-114) + z * ((-118) + z * ((-188) + z * ((-124) + z * (30 + z * (12 + z * (7 + z * (61 + z * 33))))))))))))))))))))))))))))))))))))))

theorem pow18_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_34 z * pow18_34 z = pow18_68_q z * f z + pow18_68 z + (139 : R) * pow18_68_mul_t z := by
  simp only [pow18_34, pow18_68_q, f, pow18_68, pow18_68_mul_t]
  
  ring

theorem pow18_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_34 z * pow18_34 z = pow18_68_q z * f z + pow18_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_68_mul_integer z


theorem pow18_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_34 z * pow18_34 z = pow18_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_68_mul z


theorem pow18_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 68 = pow18_68 z := by
  calc
    _ = u17 z ^ 34 * u17 z ^ 34 := by ring
    _ = pow18_34 z * pow18_34 z := by rw [pow18_34_pow z hz]
    _ = _ := pow18_68_root z hz


def pow18_69 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (1 + z * (68 + z * (42 + z * (62 + z * (26 + z * (114 + z * (30 + z * (120 + z * (73 + z * (56 + z * (94 + z * (91 + z * (82 + z * (135 + z * (38 + z * (133 + z * (50 + z * (22 + z * 38)))))))))))))))))))

def pow18_69_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (83 + z * (36 + z * (121 + z * (61 + z * (67 + z * (133 + z * (42 + z * (115 + z * (44 + z * (5 + z * (87 + z * (82 + z * (82 + z * (27 + z * (136 + z * (76 + z * (95 + z * 24))))))))))))))))))

def pow18_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-95) + z * ((-131) + z * ((-215) + z * ((-181) + z * ((-164) + z * ((-188) + z * ((-189) + z * ((-174) + z * ((-176) + z * ((-179) + z * ((-128) + z * ((-72) + z * ((-142) + z * ((-80) + z * ((-129) + z * ((-229) + z * ((-104) + z * ((-187) + z * ((-36) + z * (76 + z * (66 + z * ((-13) + z * (230 + z * (37 + z * (84 + z * (80 + z * (32 + z * (199 + z * (70 + z * (20 + z * (117 + z * (85 + z * (71 + z * (80 + z * (20 + z * (74 + z * (14 + z * 125))))))))))))))))))))))))))))))))))))))

theorem pow18_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_68 z * u17 z = pow18_69_q z * f z + pow18_69 z + (139 : R) * pow18_69_mul_t z := by
  simp only [pow18_68, u17, pow18_69_q, f, pow18_69, pow18_69_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_68 z * u17 z = pow18_69_q z * f z + pow18_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_69_mul_integer z


theorem pow18_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_68 z * u17 z = pow18_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_69_mul z


theorem pow18_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 69 = pow18_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow18_68_pow z hz]
  exact pow18_69_root z hz


def pow18_138 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (95 + z * (134 + z * (68 + z * (58 + z * (71 + z * (27 + z * (114 + z * (60 + z * (84 + z * (44 + z * (125 + z * (127 + z * (132 + z * (10 + z * (108 + z * (60 + z * (14 + z * (91 + z * 42)))))))))))))))))))

def pow18_138_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (72 + z * (97 + z * (35 + z * (101 + z * (50 + z * (94 + z * (59 + z * (59 + z * (134 + z * (117 + z * (119 + z * (46 + z * (79 + z * (88 + z * (59 + z * (72 + z * (42 + z * 54))))))))))))))))))

def pow18_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-157) + z * ((-132) + z * ((-219) + z * ((-220) + z * ((-258) + z * ((-117) + z * ((-302) + z * ((-106) + z * ((-330) + z * ((-355) + z * ((-349) + z * ((-262) + z * ((-392) + z * ((-169) + z * ((-359) + z * ((-133) + z * ((-247) + z * ((-261) + z * ((-298) + z * ((-152) + z * ((-153) + z * (49 + z * ((-100) + z * ((-38) + z * ((-3) + z * ((-46) + z * (3 + z * (5 + z * ((-76) + z * (70 + z * ((-19) + z * ((-5) + z * ((-13) + z * ((-72) + z * ((-9) + z * ((-48) + z * ((-38) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow18_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_69 z * pow18_69 z = pow18_138_q z * f z + pow18_138 z + (139 : R) * pow18_138_mul_t z := by
  simp only [pow18_69, pow18_138_q, f, pow18_138, pow18_138_mul_t]
  
  ring

theorem pow18_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_69 z * pow18_69 z = pow18_138_q z * f z + pow18_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_138_mul_integer z


theorem pow18_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_69 z * pow18_69 z = pow18_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_138_mul z


theorem pow18_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 138 = pow18_138 z := by
  calc
    _ = u17 z ^ 69 * u17 z ^ 69 := by ring
    _ = pow18_69 z * pow18_69 z := by rw [pow18_69_pow z hz]
    _ = _ := pow18_138_root z hz


def pow18_139 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (10 + z * (112 + z * (54 + z * (135 + z * (70 + z * (46 + z * (28 + z * (90 + z * (123 + z * (68 + z * (75 + z * (129 + z * (32 + z * (65 + z * (132 + z * (102 + z * (14 + z * (106 + z * 38)))))))))))))))))))

def pow18_139_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (78 + z * (90 + z * (25 + z * (134 + z * (40 + z * (5 + z * (60 + z * (34 + z * (68 + z * (113 + z * (18 + z * (84 + z * (49 + z * (131 + z * (29 + z * (104 + z * (13 + z * 52))))))))))))))))))

def pow18_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-10) + z * ((-51) + z * ((-99) + z * ((-126) + z * ((-182) + z * ((-156) + z * ((-102) + z * ((-56) + z * ((-53) + z * ((-43) + z * ((-119) + z * ((-113) + z * ((-119) + z * ((-61) + z * ((-162) + z * (43 + z * ((-23) + z * ((-77) + z * ((-68) + z * (82 + z * ((-97) + z * (247 + z * (79 + z * ((-64) + z * (197 + z * (88 + z * (118 + z * (159 + z * (68 + z * ((-52) + z * (201 + z * (29 + z * (44 + z * (2 + z * (18 + z * (19 + z * (2 + z * (40 + z * 38))))))))))))))))))))))))))))))))))))))

theorem pow18_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_138 z * u17 z = pow18_139_q z * f z + pow18_139 z + (139 : R) * pow18_139_mul_t z := by
  simp only [pow18_138, u17, pow18_139_q, f, pow18_139, pow18_139_mul_t]
  simp only [pow17_139]
  ring

theorem pow18_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow18_138 z * u17 z = pow18_139_q z * f z + pow18_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow18_139_mul_integer z


theorem pow18_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow18_138 z * u17 z = pow18_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_139_mul z


theorem pow18_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u17 z ^ 139 = pow18_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow18_138_pow z hz]
  exact pow18_139_root z hz


abbrev u18 {R : Type*} [CommRing R] (z : R) : R := pow18_139 z

theorem iterate18 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 18) = u18 z := by
  calc
    _ = (z ^ (139 ^ 17)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u17 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate17 z hz)
    _ = _ := pow18_139_pow z hz

end DimensionTen.Mod139

end

end OAI
