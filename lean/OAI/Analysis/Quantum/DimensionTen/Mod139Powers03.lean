import OAI.Analysis.Quantum.DimensionTen.Mod139Powers02

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow5_2 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (19 + z * (79 + z * (96 + z * (15 + z * (31 + z * (8 + z * (97 + z * (88 + z * (125 + z * (47 + z * (16 + z * (133 + z * (122 + z * (51 + z * (76 + z * (115 + z * (47 + z * (128 + z * 33)))))))))))))))))))

def pow5_2_q {R : Type*} [CommRing R] (z : R) : R := (114 + z * (45 + z * (137 + z * (1 + z * (18 + z * (82 + z * (129 + z * (74 + z * (40 + z * (23 + z * (61 + z * (132 + z * (21 + z * (81 + z * (5 + z * (75 + z * (113 + z * (105 + z * 30))))))))))))))))))

def pow5_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-50) + z * ((-78) + z * ((-115) + z * ((-56) + z * ((-85) + z * (41 + z * ((-89) + z * ((-60) + z * (18 + z * ((-87) + z * (123 + z * (8 + z * (78 + z * ((-82) + z * ((-120) + z * ((-71) + z * (18 + z * (235 + z * (2 + z * (161 + z * ((-51) + z * ((-16) + z * (366 + z * (150 + z * (355 + z * (95 + z * (61 + z * (64 + z * (109 + z * (94 + z * (2 + z * (91 + z * (80 + z * (237 + z * (130 + z * (49 + z * (65 + z * ((-3) + z * 114))))))))))))))))))))))))))))))))))))))

theorem pow5_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z + (139 : R) * pow5_2_mul_t z := by
  simp only [u4, pow5_2_q, f, pow5_2, pow5_2_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_2_mul_integer z


theorem pow5_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z * u4 z = pow5_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_2_mul z


theorem pow5_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 2 = pow5_2 z := by
  calc
    _ = u4 z ^ 1 * u4 z ^ 1 := by ring
    _ = u4 z * u4 z := by simp only [pow_one]
    _ = _ := pow5_2_root z hz


def pow5_4 {R : Type*} [CommRing R] (z : R) : R := (60 + z * (120 + z * (84 + z * (105 + z * (14 + z * (1 + z * (52 + z * (128 + z * (46 + z * (132 + z * (94 + z * (52 + z * (23 + z * (57 + z * (17 + z * (89 + z * (72 + z * (98 + z * (87 + z * 101)))))))))))))))))))

def pow5_4_q {R : Type*} [CommRing R] (z : R) : R := (91 + z * (94 + z * (51 + z * (118 + z * (96 + z * (59 + z * (70 + z * (57 + z * (22 + z * (29 + z * (22 + z * (116 + z * (87 + z * (79 + z * (60 + z * (8 + z * (82 + z * (133 + z * 116))))))))))))))))))

def pow5_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-146) + z * ((-177) + z * ((-255) + z * ((-307) + z * ((-262) + z * ((-309) + z * ((-353) + z * ((-311) + z * ((-245) + z * ((-195) + z * ((-210) + z * ((-221) + z * ((-466) + z * ((-351) + z * ((-157) + z * ((-206) + z * ((-235) + z * ((-258) + z * ((-333) + z * ((-201) + z * ((-32) + z * ((-103) + z * ((-3) + z * (42 + z * (221 + z * (45 + z * (32 + z * (167 + z * (51 + z * (48 + z * (86 + z * ((-21) + z * ((-5) + z * (99 + z * ((-32) + z * ((-68) + z * ((-47) + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow5_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z + (139 : R) * pow5_4_mul_t z := by
  simp only [pow5_2, pow5_4_q, f, pow5_4, pow5_4_mul_t]
  
  ring

theorem pow5_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_4_mul_integer z


theorem pow5_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_2 z * pow5_2 z = pow5_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_4_mul z


theorem pow5_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 4 = pow5_4 z := by
  calc
    _ = u4 z ^ 2 * u4 z ^ 2 := by ring
    _ = pow5_2 z * pow5_2 z := by rw [pow5_2_pow z hz]
    _ = _ := pow5_4_root z hz


def pow5_8 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (127 + z * (81 + z * (36 + z * (126 + z * (84 + z * (137 + z * (20 + z * (56 + z * (79 + z * (51 + z * (54 + z * (5 + z * (123 + z * (35 + z * (55 + z * (50 + z * (128 + z * (130 + z * 113)))))))))))))))))))

def pow5_8_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (7 + z * (107 + z * (127 + z * (10 + z * (127 + z * (118 + z * (135 + z * (6 + z * (75 + z * (28 + z * (135 + z * (123 + z * (36 + z * (118 + z * (55 + z * (0 + z * (98 + z * 54))))))))))))))))))

def pow5_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * (50 + z * (40 + z * ((-12) + z * ((-21) + z * ((-191) + z * ((-293) + z * ((-271) + z * ((-141) + z * ((-125) + z * (24 + z * ((-110) + z * ((-245) + z * ((-320) + z * ((-357) + z * ((-505) + z * ((-199) + z * ((-84) + z * ((-108) + z * ((-53) + z * ((-61) + z * ((-406) + z * ((-180) + z * ((-142) + z * ((-135) + z * ((-45) + z * (143 + z * ((-72) + z * (91 + z * (25 + z * ((-194) + z * ((-57) + z * (61 + z * ((-28) + z * (192 + z * (155 + z * (67 + z * (76 + z * 73))))))))))))))))))))))))))))))))))))))

theorem pow5_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z + (139 : R) * pow5_8_mul_t z := by
  simp only [pow5_4, pow5_8_q, f, pow5_8, pow5_8_mul_t]
  
  ring

theorem pow5_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_4 z * pow5_4 z = pow5_8_q z * f z + pow5_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_8_mul_integer z


theorem pow5_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_4 z * pow5_4 z = pow5_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_8_mul z


theorem pow5_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 8 = pow5_8 z := by
  calc
    _ = u4 z ^ 4 * u4 z ^ 4 := by ring
    _ = pow5_4 z * pow5_4 z := by rw [pow5_4_pow z hz]
    _ = _ := pow5_8_root z hz


def pow5_16 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (14 + z * (131 + z * (118 + z * (15 + z * (17 + z * (57 + z * (56 + z * (74 + z * (43 + z * (41 + z * (26 + z * (138 + z * (119 + z * (30 + z * (41 + z * (0 + z * (95 + z * (36 + z * 12)))))))))))))))))))

def pow5_16_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (110 + z * (16 + z * (0 + z * (137 + z * (109 + z * (55 + z * (119 + z * (101 + z * (54 + z * (103 + z * (106 + z * (91 + z * (15 + z * (77 + z * (23 + z * (19 + z * (120 + z * 120))))))))))))))))))

def pow5_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-126) + z * ((-48) + z * ((-34) + z * ((-145) + z * ((-38) + z * (5 + z * ((-36) + z * ((-187) + z * ((-189) + z * ((-104) + z * ((-250) + z * ((-177) + z * ((-338) + z * ((-283) + z * ((-184) + z * ((-265) + z * ((-222) + z * ((-192) + z * (5 + z * ((-220) + z * ((-22) + z * (97 + z * (90 + z * (12 + z * ((-76) + z * ((-129) + z * ((-151) + z * (19 + z * ((-9) + z * ((-23) + z * (53 + z * (171 + z * ((-13) + z * (165 + z * (215 + z * (131 + z * (100 + z * 91))))))))))))))))))))))))))))))))))))))

theorem pow5_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z + (139 : R) * pow5_16_mul_t z := by
  simp only [pow5_8, pow5_16_q, f, pow5_16, pow5_16_mul_t]
  
  ring

theorem pow5_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_8 z * pow5_8 z = pow5_16_q z * f z + pow5_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_16_mul_integer z


theorem pow5_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_8 z * pow5_8 z = pow5_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_16_mul z


theorem pow5_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 16 = pow5_16 z := by
  calc
    _ = u4 z ^ 8 * u4 z ^ 8 := by ring
    _ = pow5_8 z * pow5_8 z := by rw [pow5_8_pow z hz]
    _ = _ := pow5_16_root z hz


def pow5_17 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (46 + z * (4 + z * (69 + z * (118 + z * (111 + z * (134 + z * (95 + z * (95 + z * (11 + z * (60 + z * (3 + z * (24 + z * (29 + z * (61 + z * (109 + z * (99 + z * (9 + z * (13 + z * 114)))))))))))))))))))

def pow5_17_q {R : Type*} [CommRing R] (z : R) : R := (75 + z * (52 + z * (19 + z * (43 + z * (137 + z * (18 + z * (29 + z * (107 + z * (34 + z * (1 + z * (100 + z * (47 + z * (5 + z * (93 + z * (20 + z * (64 + z * (55 + z * (69 + z * 122))))))))))))))))))

def pow5_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-44) + z * ((-88) + z * ((-35) + z * ((-21) + z * ((-99) + z * ((-7) + z * ((-82) + z * ((-137) + z * ((-72) + z * ((-10) + z * ((-63) + z * ((-39) + z * (90 + z * ((-87) + z * ((-160) + z * (42 + z * ((-46) + z * ((-14) + z * (6 + z * ((-117) + z * ((-143) + z * (61 + z * (113 + z * ((-146) + z * (1 + z * ((-72) + z * ((-129) + z * (142 + z * (5 + z * ((-23) + z * ((-21) + z * ((-25) + z * (11 + z * ((-51) + z * ((-55) + z * ((-56) + z * ((-55) + z * ((-79) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow5_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_16 z * u4 z = pow5_17_q z * f z + pow5_17 z + (139 : R) * pow5_17_mul_t z := by
  simp only [pow5_16, u4, pow5_17_q, f, pow5_17, pow5_17_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_16 z * u4 z = pow5_17_q z * f z + pow5_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_17_mul_integer z


theorem pow5_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_16 z * u4 z = pow5_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_17_mul z


theorem pow5_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 17 = pow5_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow5_16_pow z hz]
  exact pow5_17_root z hz


def pow5_34 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (129 + z * (8 + z * (7 + z * (35 + z * (107 + z * (78 + z * (8 + z * (69 + z * (9 + z * (70 + z * (11 + z * (7 + z * (14 + z * (5 + z * (5 + z * (77 + z * (132 + z * 2))))))))))))))))))

def pow5_34_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (37 + z * (19 + z * (111 + z * (0 + z * (76 + z * (93 + z * (39 + z * (20 + z * (60 + z * (57 + z * (53 + z * (75 + z * (61 + z * (99 + z * (107 + z * (135 + z * (109 + z * 69))))))))))))))))))

def pow5_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-38) + z * ((-95) + z * ((-117) + z * ((-16) + z * ((-7) + z * ((-13) + z * (4 + z * (91 + z * (23 + z * (73 + z * (134 + z * (35 + z * ((-102) + z * ((-83) + z * ((-215) + z * ((-353) + z * ((-396) + z * ((-451) + z * ((-288) + z * ((-62) + z * ((-186) + z * ((-71) + z * (4 + z * ((-217) + z * ((-278) + z * ((-241) + z * ((-262) + z * ((-329) + z * ((-180) + z * ((-245) + z * ((-192) + z * ((-197) + z * ((-172) + z * ((-58) + z * ((-41) + z * ((-136) + z * ((-43) + z * 93))))))))))))))))))))))))))))))))))))))

theorem pow5_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_17 z * pow5_17 z = pow5_34_q z * f z + pow5_34 z + (139 : R) * pow5_34_mul_t z := by
  simp only [pow5_17, pow5_34_q, f, pow5_34, pow5_34_mul_t]
  
  ring

theorem pow5_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_17 z * pow5_17 z = pow5_34_q z * f z + pow5_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_34_mul_integer z


theorem pow5_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_17 z * pow5_17 z = pow5_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_34_mul z


theorem pow5_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 34 = pow5_34 z := by
  calc
    _ = u4 z ^ 17 * u4 z ^ 17 := by ring
    _ = pow5_17 z * pow5_17 z := by rw [pow5_17_pow z hz]
    _ = _ := pow5_34_root z hz


def pow5_68 {R : Type*} [CommRing R] (z : R) : R := (56 + z * (130 + z * (71 + z * (136 + z * (71 + z * (128 + z * (84 + z * (26 + z * (91 + z * (82 + z * (94 + z * (31 + z * (74 + z * (48 + z * (116 + z * (26 + z * (129 + z * (103 + z * (128 + z * 96)))))))))))))))))))

def pow5_68_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (97 + z * (76 + z * (21 + z * (105 + z * (21 + z * (22 + z * (42 + z * (80 + z * (104 + z * (112 + z * (43 + z * (23 + z * (75 + z * (125 + z * (16 + z * 4))))))))))))))))

def pow5_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-50) + z * ((-121) + z * ((-82) + z * ((-218) + z * ((-294) + z * ((-221) + z * ((-52) + z * ((-118) + z * ((-294) + z * ((-225) + z * ((-397) + z * ((-329) + z * ((-418) + z * ((-437) + z * ((-512) + z * ((-461) + z * ((-478) + z * ((-492) + z * ((-248) + z * ((-516) + z * ((-479) + z * ((-223) + z * ((-171) + z * ((-373) + z * ((-315) + z * ((-166) + z * ((-237) + z * ((-207) + z * ((-282) + z * ((-259) + z * ((-141) + z * ((-77) + z * ((-112) + z * (19 + z * (109 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))

theorem pow5_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_34 z * pow5_34 z = pow5_68_q z * f z + pow5_68 z + (139 : R) * pow5_68_mul_t z := by
  simp only [pow5_34, pow5_68_q, f, pow5_68, pow5_68_mul_t]
  
  ring

theorem pow5_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_34 z * pow5_34 z = pow5_68_q z * f z + pow5_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_68_mul_integer z


theorem pow5_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_34 z * pow5_34 z = pow5_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_68_mul z


theorem pow5_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 68 = pow5_68 z := by
  calc
    _ = u4 z ^ 34 * u4 z ^ 34 := by ring
    _ = pow5_34 z * pow5_34 z := by rw [pow5_34_pow z hz]
    _ = _ := pow5_68_root z hz


def pow5_69 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (76 + z * (113 + z * (29 + z * (115 + z * (52 + z * (99 + z * (43 + z * (86 + z * (62 + z * (107 + z * (82 + z * (8 + z * (95 + z * (9 + z * (54 + z * (7 + z * (21 + z * (94 + z * 35)))))))))))))))))))

def pow5_69_q {R : Type*} [CommRing R] (z : R) : R := (124 + z * (126 + z * (74 + z * (14 + z * (95 + z * (113 + z * (47 + z * (6 + z * (138 + z * (84 + z * (95 + z * (138 + z * (80 + z * (81 + z * (20 + z * (20 + z * (14 + z * (130 + z * 3))))))))))))))))))

def pow5_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-116) + z * ((-148) + z * ((-58) + z * ((-104) + z * ((-75) + z * (30 + z * ((-31) + z * (4 + z * ((-111) + z * ((-45) + z * ((-86) + z * ((-155) + z * ((-198) + z * ((-252) + z * ((-81) + z * (25 + z * (79 + z * (23 + z * (189 + z * (113 + z * (117 + z * (305 + z * (121 + z * (161 + z * (219 + z * (117 + z * (42 + z * (196 + z * (104 + z * ((-18) + z * (181 + z * (206 + z * (331 + z * (267 + z * (192 + z * (54 + z * (122 + z * 87))))))))))))))))))))))))))))))))))))))

theorem pow5_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_68 z * u4 z = pow5_69_q z * f z + pow5_69 z + (139 : R) * pow5_69_mul_t z := by
  simp only [pow5_68, u4, pow5_69_q, f, pow5_69, pow5_69_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_68 z * u4 z = pow5_69_q z * f z + pow5_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_69_mul_integer z


theorem pow5_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_68 z * u4 z = pow5_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_69_mul z


theorem pow5_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 69 = pow5_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow5_68_pow z hz]
  exact pow5_69_root z hz


def pow5_138 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (126 + z * (36 + z * (68 + z * (21 + z * (39 + z * (115 + z * (8 + z * (38 + z * (10 + z * (118 + z * (102 + z * (81 + z * (74 + z * (22 + z * (70 + z * (115 + z * (1 + z * (24 + z * 53)))))))))))))))))))

def pow5_138_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (21 + z * (136 + z * (60 + z * (38 + z * (84 + z * (120 + z * (102 + z * (70 + z * (67 + z * (43 + z * (53 + z * (87 + z * (11 + z * (113 + z * (99 + z * (43 + z * (39 + z * 113))))))))))))))))))

def pow5_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (117 + z * (121 + z * (127 + z * ((-11) + z * (111 + z * ((-28) + z * (64 + z * ((-71) + z * (46 + z * ((-100) + z * (92 + z * (9 + z * ((-51) + z * (65 + z * ((-76) + z * ((-162) + z * ((-326) + z * ((-189) + z * ((-315) + z * ((-115) + z * ((-277) + z * ((-361) + z * ((-306) + z * ((-169) + z * ((-282) + z * ((-374) + z * ((-154) + z * ((-307) + z * ((-167) + z * ((-93) + z * ((-250) + z * ((-180) + z * ((-125) + z * ((-202) + z * ((-178) + z * ((-37) + z * ((-45) + z * ((-57) + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow5_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_69 z * pow5_69 z = pow5_138_q z * f z + pow5_138 z + (139 : R) * pow5_138_mul_t z := by
  simp only [pow5_69, pow5_138_q, f, pow5_138, pow5_138_mul_t]
  
  ring

theorem pow5_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_69 z * pow5_69 z = pow5_138_q z * f z + pow5_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_138_mul_integer z


theorem pow5_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_69 z * pow5_69 z = pow5_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_138_mul z


theorem pow5_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 138 = pow5_138 z := by
  calc
    _ = u4 z ^ 69 * u4 z ^ 69 := by ring
    _ = pow5_69 z * pow5_69 z := by rw [pow5_69_pow z hz]
    _ = _ := pow5_138_root z hz


def pow5_139 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (71 + z * (57 + z * (72 + z * (120 + z * (14 + z * (1 + z * (125 + z * (25 + z * (98 + z * (113 + z * (114 + z * (40 + z * (75 + z * (61 + z * (99 + z * (133 + z * (54 + z * (114 + z * 114)))))))))))))))))))

def pow5_139_q {R : Type*} [CommRing R] (z : R) : R := (85 + z * (104 + z * (15 + z * (23 + z * (69 + z * (73 + z * (74 + z * (121 + z * (46 + z * (48 + z * (8 + z * (138 + z * (29 + z * (34 + z * (66 + z * (78 + z * (95 + z * (79 + z * 6))))))))))))))))))

def pow5_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-45) + z * ((-25) + z * (43 + z * ((-70) + z * ((-46) + z * (20 + z * ((-146) + z * ((-68) + z * ((-107) + z * ((-75) + z * ((-54) + z * ((-82) + z * ((-41) + z * ((-178) + z * ((-7) + z * ((-36) + z * ((-116) + z * ((-36) + z * ((-76) + z * ((-8) + z * (34 + z * (21 + z * ((-109) + z * ((-140) + z * (25 + z * ((-29) + z * ((-4) + z * (83 + z * (66 + z * ((-36) + z * (41 + z * (34 + z * ((-12) + z * ((-7) + z * (20 + z * ((-36) + z * (21 + z * 48))))))))))))))))))))))))))))))))))))))

theorem pow5_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_138 z * u4 z = pow5_139_q z * f z + pow5_139 z + (139 : R) * pow5_139_mul_t z := by
  simp only [pow5_138, u4, pow5_139_q, f, pow5_139, pow5_139_mul_t]
  simp only [pow4_139]
  ring

theorem pow5_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow5_138 z * u4 z = pow5_139_q z * f z + pow5_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow5_139_mul_integer z


theorem pow5_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow5_138 z * u4 z = pow5_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_139_mul z


theorem pow5_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u4 z ^ 139 = pow5_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow5_138_pow z hz]
  exact pow5_139_root z hz


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_139 z

theorem iterate5 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 5) = u5 z := by
  calc
    _ = (z ^ (139 ^ 4)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u4 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate4 z hz)
    _ = _ := pow5_139_pow z hz


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (137 + z * (3 + z * (84 + z * (61 + z * (97 + z * (44 + z * (118 + z * (76 + z * (88 + z * (118 + z * (131 + z * (132 + z * (91 + z * (110 + z * (28 + z * (51 + z * (101 + z * (71 + z * 14)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (32 + z * (108 + z * (50 + z * (80 + z * (62 + z * (1 + z * (26 + z * (6 + z * (16 + z * (77 + z * (56 + z * (121 + z * (60 + z * (76 + z * (24 + z * (59 + z * (63 + z * 69))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-55) + z * ((-104) + z * ((-136) + z * ((-162) + z * ((-119) + z * ((-131) + z * ((-118) + z * (7 + z * ((-86) + z * ((-46) + z * (61 + z * ((-103) + z * ((-88) + z * ((-13) + z * ((-141) + z * ((-36) + z * (72 + z * (61 + z * (157 + z * (247 + z * (110 + z * (301 + z * (292 + z * (155 + z * (319 + z * (367 + z * (253 + z * (284 + z * (327 + z * (178 + z * (121 + z * (197 + z * (181 + z * (278 + z * (206 + z * (73 + z * (123 + z * 93))))))))))))))))))))))))))))))))))))))

theorem pow6_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z + (139 : R) * pow6_2_mul_t z := by
  simp only [u5, pow6_2_q, f, pow6_2, pow6_2_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_2_mul_integer z


theorem pow6_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z * u5 z = pow6_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_2_mul z


theorem pow6_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 2 = pow6_2 z := by
  calc
    _ = u5 z ^ 1 * u5 z ^ 1 := by ring
    _ = u5 z * u5 z := by simp only [pow_one]
    _ = _ := pow6_2_root z hz


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (34 + z * (133 + z * (87 + z * (28 + z * (74 + z * (52 + z * (45 + z * (130 + z * (120 + z * (2 + z * (36 + z * (109 + z * (21 + z * (88 + z * (8 + z * (4 + z * (124 + z * (71 + z * 20)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (85 + z * (25 + z * (63 + z * (41 + z * (98 + z * (46 + z * (109 + z * (4 + z * (127 + z * (131 + z * (6 + z * (71 + z * (75 + z * (134 + z * (31 + z * (73 + z * (101 + z * (113 + z * 57))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-51) + z * ((-7) + z * ((-10) + z * ((-131) + z * ((-53) + z * ((-78) + z * ((-64) + z * ((-101) + z * (12 + z * ((-171) + z * ((-33) + z * (52 + z * (107 + z * (35 + z * (141 + z * (119 + z * ((-51) + z * (125 + z * (69 + z * (48 + z * (127 + z * (165 + z * (127 + z * (221 + z * (149 + z * (123 + z * (81 + z * ((-35) + z * (88 + z * (105 + z * (25 + z * ((-94) + z * ((-137) + z * ((-89) + z * ((-58) + z * ((-63) + z * ((-90) + z * ((-39) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow6_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z + (139 : R) * pow6_4_mul_t z := by
  simp only [pow6_2, pow6_4_q, f, pow6_4, pow6_4_mul_t]
  
  ring

theorem pow6_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_4_mul_integer z


theorem pow6_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_2 z * pow6_2 z = pow6_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_4_mul z


theorem pow6_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 4 = pow6_4 z := by
  calc
    _ = u5 z ^ 2 * u5 z ^ 2 := by ring
    _ = pow6_2 z * pow6_2 z := by rw [pow6_2_pow z hz]
    _ = _ := pow6_4_root z hz


def pow6_8 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (129 + z * (60 + z * (82 + z * (72 + z * (20 + z * (40 + z * (8 + z * (137 + z * (85 + z * (123 + z * (128 + z * (63 + z * (111 + z * (18 + z * (50 + z * (106 + z * (52 + z * (108 + z * 64)))))))))))))))))))

def pow6_8_q {R : Type*} [CommRing R] (z : R) : R := (84 + z * (3 + z * (61 + z * (120 + z * (128 + z * (18 + z * (122 + z * (115 + z * (116 + z * (86 + z * (23 + z * (120 + z * (107 + z * (69 + z * (75 + z * (19 + z * (52 + z * (12 + z * 122))))))))))))))))))

def pow6_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-28) + z * (75 + z * ((-37) + z * ((-116) + z * ((-33) + z * ((-196) + z * ((-225) + z * ((-116) + z * ((-171) + z * ((-211) + z * ((-126) + z * ((-274) + z * ((-441) + z * ((-133) + z * ((-374) + z * ((-406) + z * ((-104) + z * ((-416) + z * ((-337) + z * ((-133) + z * ((-384) + z * ((-468) + z * ((-222) + z * ((-315) + z * ((-226) + z * ((-44) + z * ((-366) + z * ((-249) + z * ((-59) + z * ((-162) + z * ((-108) + z * ((-111) + z * ((-131) + z * ((-41) + z * (71 + z * ((-29) + z * ((-92) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow6_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z + (139 : R) * pow6_8_mul_t z := by
  simp only [pow6_4, pow6_8_q, f, pow6_8, pow6_8_mul_t]
  
  ring

theorem pow6_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_4 z * pow6_4 z = pow6_8_q z * f z + pow6_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_8_mul_integer z


theorem pow6_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_4 z * pow6_4 z = pow6_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_8_mul z


theorem pow6_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 8 = pow6_8 z := by
  calc
    _ = u5 z ^ 4 * u5 z ^ 4 := by ring
    _ = pow6_4 z * pow6_4 z := by rw [pow6_4_pow z hz]
    _ = _ := pow6_8_root z hz


def pow6_16 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (67 + z * (13 + z * (79 + z * (86 + z * (24 + z * (53 + z * (57 + z * (113 + z * (131 + z * (44 + z * (103 + z * (103 + z * (62 + z * (28 + z * (34 + z * (40 + z * (27 + z * (86 + z * 57)))))))))))))))))))

def pow6_16_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (47 + z * (94 + z * (134 + z * (59 + z * (71 + z * (121 + z * (43 + z * (72 + z * (37 + z * (34 + z * (101 + z * (37 + z * (32 + z * (42 + z * (121 + z * (93 + z * (83 + z * 65))))))))))))))))))

def pow6_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (56 + z * (31 + z * ((-72) + z * ((-74) + z * ((-140) + z * ((-249) + z * ((-246) + z * ((-192) + z * ((-65) + z * ((-56) + z * (62 + z * (68 + z * (10 + z * (85 + z * ((-225) + z * ((-129) + z * ((-62) + z * ((-128) + z * (93 + z * (67 + z * (28 + z * (16 + z * (68 + z * ((-7) + z * ((-67) + z * (201 + z * (178 + z * (197 + z * (210 + z * ((-21) + z * (6 + z * (30 + z * ((-65) + z * ((-4) + z * (31 + z * (7 + z * (39 + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow6_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z + (139 : R) * pow6_16_mul_t z := by
  simp only [pow6_8, pow6_16_q, f, pow6_16, pow6_16_mul_t]
  
  ring

theorem pow6_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_8 z * pow6_8 z = pow6_16_q z * f z + pow6_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_16_mul_integer z


theorem pow6_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_8 z * pow6_8 z = pow6_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_16_mul z


theorem pow6_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 16 = pow6_16 z := by
  calc
    _ = u5 z ^ 8 * u5 z ^ 8 := by ring
    _ = pow6_8 z * pow6_8 z := by rw [pow6_8_pow z hz]
    _ = _ := pow6_16_root z hz


def pow6_17 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (86 + z * (75 + z * (126 + z * (81 + z * (130 + z * (117 + z * (68 + z * (29 + z * (127 + z * (4 + z * (137 + z * (106 + z * (42 + z * (116 + z * (24 + z * (138 + z * (104 + z * (95 + z * 69)))))))))))))))))))

def pow6_17_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (50 + z * (64 + z * (27 + z * (23 + z * (127 + z * (105 + z * (101 + z * (47 + z * (21 + z * (107 + z * (70 + z * (126 + z * (23 + z * (53 + z * (20 + z * (17 + z * (71 + z * 104))))))))))))))))))

def pow6_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-4) + z * ((-36) + z * ((-55) + z * (10 + z * ((-97) + z * ((-205) + z * ((-125) + z * ((-204) + z * ((-209) + z * ((-82) + z * ((-67) + z * ((-131) + z * ((-75) + z * ((-192) + z * ((-137) + z * (5 + z * ((-47) + z * ((-34) + z * (77 + z * ((-106) + z * ((-135) + z * (155 + z * (84 + z * ((-20) + z * (17 + z * (49 + z * (142 + z * (120 + z * (133 + z * (34 + z * ((-6) + z * (49 + z * ((-11) + z * (76 + z * (75 + z * ((-27) + z * (21 + z * 46))))))))))))))))))))))))))))))))))))))

theorem pow6_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_16 z * u5 z = pow6_17_q z * f z + pow6_17 z + (139 : R) * pow6_17_mul_t z := by
  simp only [pow6_16, u5, pow6_17_q, f, pow6_17, pow6_17_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_16 z * u5 z = pow6_17_q z * f z + pow6_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_17_mul_integer z


theorem pow6_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_16 z * u5 z = pow6_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_17_mul z


theorem pow6_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 17 = pow6_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow6_16_pow z hz]
  exact pow6_17_root z hz


def pow6_34 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (20 + z * (85 + z * (129 + z * (56 + z * (73 + z * (116 + z * (88 + z * (86 + z * (85 + z * (72 + z * (25 + z * (41 + z * (133 + z * (128 + z * (74 + z * (132 + z * (45 + z * (67 + z * 138)))))))))))))))))))

def pow6_34_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (110 + z * (11 + z * (65 + z * (92 + z * (72 + z * (97 + z * (94 + z * (134 + z * (101 + z * (136 + z * (14 + z * (66 + z * (50 + z * (69 + z * (37 + z * (62 + z * (12 + z * 35))))))))))))))))))

def pow6_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (15 + z * ((-24) + z * ((-1) + z * (22 + z * (11 + z * (38 + z * (122 + z * (78 + z * (16 + z * (16 + z * ((-98) + z * ((-90) + z * (109 + z * ((-26) + z * (90 + z * (149 + z * (71 + z * (200 + z * (308 + z * (215 + z * (361 + z * (388 + z * (278 + z * (334 + z * (98 + z * (258 + z * (44 + z * (185 + z * (262 + z * (167 + z * (389 + z * (178 + z * (202 + z * (231 + z * (181 + z * (213 + z * (131 + z * (62 + z * 34))))))))))))))))))))))))))))))))))))))

theorem pow6_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_17 z * pow6_17 z = pow6_34_q z * f z + pow6_34 z + (139 : R) * pow6_34_mul_t z := by
  simp only [pow6_17, pow6_34_q, f, pow6_34, pow6_34_mul_t]
  
  ring

theorem pow6_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_17 z * pow6_17 z = pow6_34_q z * f z + pow6_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_34_mul_integer z


theorem pow6_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_17 z * pow6_17 z = pow6_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_34_mul z


theorem pow6_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 34 = pow6_34 z := by
  calc
    _ = u5 z ^ 17 * u5 z ^ 17 := by ring
    _ = pow6_17 z * pow6_17 z := by rw [pow6_17_pow z hz]
    _ = _ := pow6_34_root z hz


def pow6_68 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (46 + z * (120 + z * (15 + z * (55 + z * (69 + z * (105 + z * (89 + z * (112 + z * (74 + z * (103 + z * (100 + z * (126 + z * (107 + z * (75 + z * (115 + z * (109 + z * (45 + z * (27 + z * 21)))))))))))))))))))

def pow6_68_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (124 + z * (137 + z * (132 + z * (116 + z * (55 + z * (106 + z * (30 + z * (17 + z * (123 + z * (77 + z * (138 + z * (1 + z * (135 + z * (68 + z * (100 + z * (25 + z * (16 + z * 1))))))))))))))))))

def pow6_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (64 + z * ((-74) + z * ((-97) + z * ((-131) + z * ((-283) + z * ((-214) + z * ((-131) + z * ((-116) + z * (9 + z * (15 + z * ((-88) + z * ((-240) + z * ((-170) + z * ((-128) + z * ((-160) + z * ((-119) + z * (73 + z * ((-71) + z * (85 + z * (238 + z * (81 + z * (276 + z * (328 + z * (217 + z * (171 + z * (226 + z * (281 + z * (247 + z * (202 + z * (184 + z * (183 + z * (225 + z * (355 + z * (260 + z * (177 + z * (270 + z * (106 + z * (132 + z * 137))))))))))))))))))))))))))))))))))))))

theorem pow6_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_34 z * pow6_34 z = pow6_68_q z * f z + pow6_68 z + (139 : R) * pow6_68_mul_t z := by
  simp only [pow6_34, pow6_68_q, f, pow6_68, pow6_68_mul_t]
  
  ring

theorem pow6_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_34 z * pow6_34 z = pow6_68_q z * f z + pow6_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_68_mul_integer z


theorem pow6_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_34 z * pow6_34 z = pow6_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_68_mul z


theorem pow6_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 68 = pow6_68 z := by
  calc
    _ = u5 z ^ 34 * u5 z ^ 34 := by ring
    _ = pow6_34 z * pow6_34 z := by rw [pow6_34_pow z hz]
    _ = _ := pow6_68_root z hz


def pow6_69 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (85 + z * (124 + z * (43 + z * (78 + z * (5 + z * (97 + z * (73 + z * (36 + z * (115 + z * (93 + z * (35 + z * (75 + z * (102 + z * (116 + z * (49 + z * (56 + z * (14 + z * (52 + z * 64)))))))))))))))))))

def pow6_69_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (40 + z * (17 + z * (98 + z * (74 + z * (60 + z * (20 + z * (24 + z * (114 + z * (52 + z * (85 + z * (91 + z * (29 + z * (35 + z * (112 + z * (74 + z * (67 + z * (114 + z * 31))))))))))))))))))

def pow6_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-5) + z * ((-5) + z * ((-19) + z * ((-70) + z * ((-105) + z * ((-80) + z * ((-73) + z * ((-74) + z * (50 + z * ((-56) + z * ((-47) + z * ((-45) + z * (15 + z * ((-20) + z * (109 + z * (97 + z * (41 + z * (15 + z * (123 + z * (189 + z * (149 + z * (225 + z * (214 + z * (146 + z * (310 + z * (232 + z * (119 + z * (235 + z * (158 + z * (89 + z * (214 + z * (97 + z * ((-3) + z * (98 + z * (11 + z * ((-61) + z * (10 + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow6_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_68 z * u5 z = pow6_69_q z * f z + pow6_69 z + (139 : R) * pow6_69_mul_t z := by
  simp only [pow6_68, u5, pow6_69_q, f, pow6_69, pow6_69_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_68 z * u5 z = pow6_69_q z * f z + pow6_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_69_mul_integer z


theorem pow6_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_68 z * u5 z = pow6_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_69_mul z


theorem pow6_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 69 = pow6_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow6_68_pow z hz]
  exact pow6_69_root z hz


def pow6_138 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (108 + z * (39 + z * (23 + z * (93 + z * (16 + z * (85 + z * (14 + z * (95 + z * (103 + z * (47 + z * (26 + z * (125 + z * (126 + z * (99 + z * (30 + z * (119 + z * (61 + z * (7 + z * 13)))))))))))))))))))

def pow6_138_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (11 + z * (75 + z * (90 + z * (56 + z * (110 + z * (44 + z * (9 + z * (48 + z * (138 + z * (65 + z * (117 + z * (70 + z * (105 + z * (96 + z * (99 + z * (134 + z * (4 + z * 65))))))))))))))))))

def pow6_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-33) + z * ((-3) + z * ((-66) + z * ((-56) + z * ((-153) + z * ((-117) + z * ((-115) + z * ((-16) + z * ((-131) + z * ((-80) + z * ((-93) + z * ((-210) + z * ((-245) + z * ((-132) + z * ((-181) + z * ((-173) + z * ((-225) + z * ((-393) + z * ((-315) + z * ((-70) + z * ((-198) + z * ((-157) + z * ((-124) + z * ((-269) + z * ((-138) + z * ((-100) + z * ((-146) + z * ((-119) + z * ((-187) + z * ((-159) + z * ((-165) + z * ((-96) + z * ((-52) + z * ((-156) + z * ((-65) + z * ((-20) + z * ((-12) + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow6_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_69 z * pow6_69 z = pow6_138_q z * f z + pow6_138 z + (139 : R) * pow6_138_mul_t z := by
  simp only [pow6_69, pow6_138_q, f, pow6_138, pow6_138_mul_t]
  
  ring

theorem pow6_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_69 z * pow6_69 z = pow6_138_q z * f z + pow6_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_138_mul_integer z


theorem pow6_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_69 z * pow6_69 z = pow6_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_138_mul z


theorem pow6_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 138 = pow6_138 z := by
  calc
    _ = u5 z ^ 69 * u5 z ^ 69 := by ring
    _ = pow6_69 z * pow6_69 z := by rw [pow6_69_pow z hz]
    _ = _ := pow6_138_root z hz


def pow6_139 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (101 + z * (26 + z * (11 + z * (7 + z * (135 + z * (89 + z * (129 + z * (14 + z * (135 + z * (13 + z * (52 + z * (21 + z * (43 + z * (42 + z * (50 + z * (103 + z * (62 + z * (67 + z * 28)))))))))))))))))))

def pow6_139_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (61 + z * (25 + z * (46 + z * (7 + z * (82 + z * (124 + z * (44 + z * (49 + z * (4 + z * (46 + z * (130 + z * (107 + z * (108 + z * (82 + z * (24 + z * (115 + z * (95 + z * 92))))))))))))))))))

def pow6_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-100) + z * ((-155) + z * ((-130) + z * ((-165) + z * ((-133) + z * ((-50) + z * ((-197) + z * ((-225) + z * ((-168) + z * ((-261) + z * ((-179) + z * ((-78) + z * ((-152) + z * ((-247) + z * ((-340) + z * ((-273) + z * ((-254) + z * ((-31) + z * ((-260) + z * ((-213) + z * ((-88) + z * ((-227) + z * ((-61) + z * (132 + z * ((-45) + z * ((-33) + z * ((-94) + z * (16 + z * (109 + z * ((-31) + z * ((-55) + z * ((-6) + z * (8 + z * ((-11) + z * ((-22) + z * ((-13) + z * ((-95) + z * ((-69) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow6_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_138 z * u5 z = pow6_139_q z * f z + pow6_139 z + (139 : R) * pow6_139_mul_t z := by
  simp only [pow6_138, u5, pow6_139_q, f, pow6_139, pow6_139_mul_t]
  simp only [pow5_139]
  ring

theorem pow6_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow6_138 z * u5 z = pow6_139_q z * f z + pow6_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow6_139_mul_integer z


theorem pow6_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow6_138 z * u5 z = pow6_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_139_mul z


theorem pow6_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u5 z ^ 139 = pow6_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow6_138_pow z hz]
  exact pow6_139_root z hz


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_139 z

theorem iterate6 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 6) = u6 z := by
  calc
    _ = (z ^ (139 ^ 5)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate5 z hz)
    _ = _ := pow6_139_pow z hz

end DimensionTen.Mod139

end

end OAI
