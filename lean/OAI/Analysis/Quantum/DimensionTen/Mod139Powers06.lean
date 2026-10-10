import OAI.Analysis.Quantum.DimensionTen.Mod139Powers05

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow11_2 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (48 + z * (100 + z * (115 + z * (22 + z * (109 + z * (61 + z * (73 + z * (11 + z * (108 + z * (59 + z * (37 + z * (29 + z * (33 + z * (5 + z * (124 + z * (68 + z * (11 + z * (45 + z * 9)))))))))))))))))))

def pow11_2_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (70 + z * (122 + z * (77 + z * (123 + z * (16 + z * (46 + z * (33 + z * (83 + z * (119 + z * (124 + z * (63 + z * (102 + z * (137 + z * (123 + z * (54 + z * (11 + z * (41 + z * 71))))))))))))))))))

def pow11_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-62) + z * ((-122) + z * ((-184) + z * ((-190) + z * ((-269) + z * ((-280) + z * ((-234) + z * ((-163) + z * ((-239) + z * ((-352) + z * ((-384) + z * ((-427) + z * ((-556) + z * ((-573) + z * ((-438) + z * ((-450) + z * ((-596) + z * ((-522) + z * ((-390) + z * ((-354) + z * ((-363) + z * ((-330) + z * ((-317) + z * ((-354) + z * ((-246) + z * ((-187) + z * ((-136) + z * ((-231) + z * ((-297) + z * ((-109) + z * (23 + z * ((-30) + z * ((-78) + z * ((-74) + z * (67 + z * (144 + z * (36 + z * ((-11) + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow11_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z + (139 : R) * pow11_2_mul_t z := by
  simp only [u10, pow11_2_q, f, pow11_2, pow11_2_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_2_mul_integer z


theorem pow11_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z * u10 z = pow11_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_2_mul z


theorem pow11_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 2 = pow11_2 z := by
  calc
    _ = u10 z ^ 1 * u10 z ^ 1 := by ring
    _ = u10 z * u10 z := by simp only [pow_one]
    _ = _ := pow11_2_root z hz


def pow11_4 {R : Type*} [CommRing R] (z : R) : R := (86 + z * (49 + z * (7 + z * (43 + z * (46 + z * (23 + z * (2 + z * (27 + z * (103 + z * (12 + z * (137 + z * (0 + z * (78 + z * (97 + z * (86 + z * (65 + z * (75 + z * (76 + z * (26 + z * 102)))))))))))))))))))

def pow11_4_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (122 + z * (62 + z * (87 + z * (21 + z * (122 + z * (84 + z * (131 + z * (41 + z * (63 + z * (101 + z * (65 + z * (87 + z * (99 + z * (47 + z * (74 + z * (23 + z * (33 + z * 81))))))))))))))))))

def pow11_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-115) + z * ((-148) + z * ((-170) + z * ((-138) + z * ((-148) + z * ((-154) + z * ((-200) + z * ((-167) + z * ((-275) + z * ((-299) + z * ((-303) + z * ((-185) + z * ((-417) + z * ((-422) + z * ((-480) + z * ((-447) + z * ((-380) + z * ((-241) + z * ((-479) + z * ((-423) + z * ((-370) + z * ((-361) + z * ((-403) + z * ((-267) + z * ((-306) + z * ((-363) + z * ((-234) + z * ((-304) + z * ((-255) + z * ((-127) + z * ((-172) + z * ((-140) + z * ((-86) + z * ((-92) + z * ((-30) + z * ((-74) + z * ((-69) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z + (139 : R) * pow11_4_mul_t z := by
  simp only [pow11_2, pow11_4_q, f, pow11_4, pow11_4_mul_t]
  
  ring

theorem pow11_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_4_mul_integer z


theorem pow11_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_2 z * pow11_2 z = pow11_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_4_mul z


theorem pow11_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 4 = pow11_4 z := by
  calc
    _ = u10 z ^ 2 * u10 z ^ 2 := by ring
    _ = pow11_2 z * pow11_2 z := by rw [pow11_2_pow z hz]
    _ = _ := pow11_4_root z hz


def pow11_8 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (83 + z * (16 + z * (95 + z * (39 + z * (67 + z * (26 + z * (36 + z * (92 + z * (93 + z * (53 + z * (45 + z * (39 + z * (4 + z * (78 + z * (31 + z * (131 + z * (18 + z * (109 + z * 7)))))))))))))))))))

def pow11_8_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (107 + z * (98 + z * (99 + z * (68 + z * (128 + z * (8 + z * (3 + z * (19 + z * (98 + z * (30 + z * (6 + z * (59 + z * (29 + z * (42 + z * (122 + z * (38 + z * (69 + z * 118))))))))))))))))))

def pow11_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * ((-48) + z * ((-170) + z * ((-229) + z * ((-265) + z * ((-367) + z * ((-357) + z * ((-285) + z * ((-164) + z * ((-291) + z * ((-219) + z * ((-295) + z * ((-315) + z * ((-197) + z * ((-232) + z * ((-314) + z * ((-265) + z * ((-291) + z * ((-375) + z * ((-450) + z * ((-195) + z * ((-347) + z * ((-128) + z * ((-59) + z * ((-88) + z * ((-66) + z * (106 + z * (108 + z * ((-155) + z * (258 + z * ((-13) + z * ((-26) + z * (103 + z * ((-29) + z * ((-74) + z * (52 + z * ((-34) + z * ((-71) + z * 74))))))))))))))))))))))))))))))))))))))

theorem pow11_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z + (139 : R) * pow11_8_mul_t z := by
  simp only [pow11_4, pow11_8_q, f, pow11_8, pow11_8_mul_t]
  
  ring

theorem pow11_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_4 z * pow11_4 z = pow11_8_q z * f z + pow11_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_8_mul_integer z


theorem pow11_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_4 z * pow11_4 z = pow11_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_8_mul z


theorem pow11_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 8 = pow11_8 z := by
  calc
    _ = u10 z ^ 4 * u10 z ^ 4 := by ring
    _ = pow11_4 z * pow11_4 z := by rw [pow11_4_pow z hz]
    _ = _ := pow11_8_root z hz


def pow11_16 {R : Type*} [CommRing R] (z : R) : R := (126 + z * (26 + z * (46 + z * (20 + z * (85 + z * (119 + z * (69 + z * (9 + z * (133 + z * (1 + z * (20 + z * (51 + z * (133 + z * (3 + z * (45 + z * (77 + z * (71 + z * (57 + z * (106 + z * 31)))))))))))))))))))

def pow11_16_q {R : Type*} [CommRing R] (z : R) : R := (73 + z * (20 + z * (19 + z * (109 + z * (31 + z * (22 + z * (42 + z * (102 + z * (69 + z * (103 + z * (25 + z * (95 + z * (114 + z * (95 + z * (47 + z * (46 + z * (104 + z * (119 + z * 49))))))))))))))))))

def pow11_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (52 + z * ((-23) + z * ((-17) + z * ((-36) + z * ((-24) + z * ((-34) + z * ((-145) + z * ((-20) + z * ((-80) + z * ((-166) + z * ((-156) + z * ((-208) + z * ((-374) + z * ((-232) + z * ((-292) + z * ((-337) + z * ((-252) + z * ((-328) + z * ((-283) + z * ((-392) + z * ((-307) + z * ((-425) + z * ((-205) + z * ((-205) + z * ((-289) + z * ((-280) + z * ((-293) + z * ((-209) + z * ((-231) + z * ((-186) + z * ((-287) + z * ((-52) + z * ((-118) + z * (51 + z * ((-142) + z * ((-59) + z * ((-35) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z + (139 : R) * pow11_16_mul_t z := by
  simp only [pow11_8, pow11_16_q, f, pow11_16, pow11_16_mul_t]
  
  ring

theorem pow11_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_8 z * pow11_8 z = pow11_16_q z * f z + pow11_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_16_mul_integer z


theorem pow11_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_8 z * pow11_8 z = pow11_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_16_mul z


theorem pow11_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 16 = pow11_16 z := by
  calc
    _ = u10 z ^ 8 * u10 z ^ 8 := by ring
    _ = pow11_8 z * pow11_8 z := by rw [pow11_8_pow z hz]
    _ = _ := pow11_16_root z hz


def pow11_17 {R : Type*} [CommRing R] (z : R) : R := (106 + z * (125 + z * (134 + z * (27 + z * (131 + z * (86 + z * (64 + z * (102 + z * (20 + z * (33 + z * (124 + z * (62 + z * (51 + z * (62 + z * (19 + z * (100 + z * (102 + z * (67 + z * (107 + z * 118)))))))))))))))))))

def pow11_17_q {R : Type*} [CommRing R] (z : R) : R := (131 + z * (95 + z * (108 + z * (81 + z * (113 + z * (9 + z * (53 + z * (88 + z * (61 + z * (17 + z * (87 + z * (87 + z * (126 + z * (31 + z * (47 + z * (51 + z * (81 + z * (114 + z * 128))))))))))))))))))

def pow11_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-97) + z * ((-120) + z * ((-171) + z * ((-281) + z * ((-362) + z * ((-246) + z * ((-167) + z * ((-232) + z * ((-257) + z * ((-212) + z * ((-349) + z * ((-389) + z * ((-427) + z * ((-300) + z * ((-336) + z * ((-474) + z * ((-434) + z * ((-264) + z * ((-401) + z * ((-513) + z * ((-471) + z * ((-280) + z * ((-311) + z * ((-163) + z * ((-93) + z * ((-232) + z * ((-308) + z * ((-245) + z * ((-157) + z * ((-45) + z * ((-142) + z * ((-151) + z * ((-57) + z * ((-85) + z * ((-43) + z * ((-3) + z * ((-87) + z * ((-67) + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow11_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_16 z * u10 z = pow11_17_q z * f z + pow11_17 z + (139 : R) * pow11_17_mul_t z := by
  simp only [pow11_16, u10, pow11_17_q, f, pow11_17, pow11_17_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_16 z * u10 z = pow11_17_q z * f z + pow11_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_17_mul_integer z


theorem pow11_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_16 z * u10 z = pow11_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_17_mul z


theorem pow11_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 17 = pow11_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow11_16_pow z hz]
  exact pow11_17_root z hz


def pow11_34 {R : Type*} [CommRing R] (z : R) : R := (51 + z * (129 + z * (86 + z * (78 + z * (50 + z * (95 + z * (32 + z * (1 + z * (73 + z * (36 + z * (5 + z * (138 + z * (89 + z * (48 + z * (7 + z * (72 + z * (134 + z * (113 + z * (0 + z * 1)))))))))))))))))))

def pow11_34_q {R : Type*} [CommRing R] (z : R) : R := (133 + z * (90 + z * (59 + z * (112 + z * (57 + z * (67 + z * (12 + z * (102 + z * (19 + z * (117 + z * (122 + z * (83 + z * (16 + z * (110 + z * (74 + z * (104 + z * (106 + z * (79 + z * 24))))))))))))))))))

def pow11_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (5 + z * (73 + z * ((-62) + z * ((-7) + z * (50 + z * (165 + z * (75 + z * (92 + z * ((-44) + z * ((-160) + z * ((-3) + z * (3 + z * ((-248) + z * ((-108) + z * ((-106) + z * ((-190) + z * ((-4) + z * ((-129) + z * ((-34) + z * (178 + z * (127 + z * (50 + z * (51 + z * ((-64) + z * ((-31) + z * ((-50) + z * ((-60) + z * ((-3) + z * ((-7) + z * (2 + z * (41 + z * (1 + z * (58 + z * (165 + z * (120 + z * (105 + z * (159 + z * 100))))))))))))))))))))))))))))))))))))))

theorem pow11_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_17 z * pow11_17 z = pow11_34_q z * f z + pow11_34 z + (139 : R) * pow11_34_mul_t z := by
  simp only [pow11_17, pow11_34_q, f, pow11_34, pow11_34_mul_t]
  
  ring

theorem pow11_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_17 z * pow11_17 z = pow11_34_q z * f z + pow11_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_34_mul_integer z


theorem pow11_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_17 z * pow11_17 z = pow11_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_34_mul z


theorem pow11_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 34 = pow11_34 z := by
  calc
    _ = u10 z ^ 17 * u10 z ^ 17 := by ring
    _ = pow11_17 z * pow11_17 z := by rw [pow11_17_pow z hz]
    _ = _ := pow11_34_root z hz


def pow11_68 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (23 + z * (22 + z * (3 + z * (120 + z * (42 + z * (45 + z * (12 + z * (57 + z * (75 + z * (44 + z * (24 + z * (39 + z * (126 + z * (126 + z * (94 + z * (4 + z * (136 + z * (93 + z * 38)))))))))))))))))))

def pow11_68_q {R : Type*} [CommRing R] (z : R) : R := (71 + z * (126 + z * (89 + z * (45 + z * (37 + z * (49 + z * (136 + z * (69 + z * (62 + z * (105 + z * (83 + z * (135 + z * (95 + z * (123 + z * (135 + z * (34 + z * (106 + z * (11 + z * 1))))))))))))))))))

def pow11_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-63) + z * ((-59) + z * ((-76) + z * ((-89) + z * ((-56) + z * ((-49) + z * ((-162) + z * ((-240) + z * ((-304) + z * ((-413) + z * ((-420) + z * ((-271) + z * ((-295) + z * ((-469) + z * ((-602) + z * ((-428) + z * ((-230) + z * ((-267) + z * ((-398) + z * ((-381) + z * ((-380) + z * ((-341) + z * ((-347) + z * ((-369) + z * ((-384) + z * ((-338) + z * ((-157) + z * (13 + z * ((-237) + z * ((-253) + z * ((-129) + z * ((-62) + z * (58 + z * ((-18) + z * ((-104) + z * ((-10) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow11_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_34 z * pow11_34 z = pow11_68_q z * f z + pow11_68 z + (139 : R) * pow11_68_mul_t z := by
  simp only [pow11_34, pow11_68_q, f, pow11_68, pow11_68_mul_t]
  
  ring

theorem pow11_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_34 z * pow11_34 z = pow11_68_q z * f z + pow11_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_68_mul_integer z


theorem pow11_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_34 z * pow11_34 z = pow11_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_68_mul z


theorem pow11_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 68 = pow11_68 z := by
  calc
    _ = u10 z ^ 34 * u10 z ^ 34 := by ring
    _ = pow11_34 z * pow11_34 z := by rw [pow11_34_pow z hz]
    _ = _ := pow11_68_root z hz


def pow11_69 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (9 + z * (97 + z * (88 + z * (130 + z * (132 + z * (14 + z * (103 + z * (78 + z * (61 + z * (15 + z * (92 + z * (25 + z * (48 + z * (110 + z * (115 + z * (63 + z * (1 + z * (62 + z * 73)))))))))))))))))))

def pow11_69_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (81 + z * (59 + z * (31 + z * (98 + z * (137 + z * (65 + z * (43 + z * (72 + z * (134 + z * (38 + z * (116 + z * (80 + z * (76 + z * (25 + z * (53 + z * (72 + z * (3 + z * 130))))))))))))))))))

def pow11_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-98) + z * ((-169) + z * ((-212) + z * ((-239) + z * ((-303) + z * ((-292) + z * ((-263) + z * ((-331) + z * ((-406) + z * ((-456) + z * ((-424) + z * ((-472) + z * ((-505) + z * ((-555) + z * ((-515) + z * ((-453) + z * ((-439) + z * ((-306) + z * ((-479) + z * ((-464) + z * ((-378) + z * ((-320) + z * ((-186) + z * ((-161) + z * ((-306) + z * ((-229) + z * (4 + z * ((-103) + z * ((-150) + z * ((-46) + z * (94 + z * (48 + z * (77 + z * (49 + z * ((-26) + z * (115 + z * (33 + z * ((-67) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow11_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_68 z * u10 z = pow11_69_q z * f z + pow11_69 z + (139 : R) * pow11_69_mul_t z := by
  simp only [pow11_68, u10, pow11_69_q, f, pow11_69, pow11_69_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_68 z * u10 z = pow11_69_q z * f z + pow11_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_69_mul_integer z


theorem pow11_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_68 z * u10 z = pow11_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_69_mul z


theorem pow11_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 69 = pow11_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow11_68_pow z hz]
  exact pow11_69_root z hz


def pow11_138 {R : Type*} [CommRing R] (z : R) : R := (105 + z * (127 + z * (0 + z * (23 + z * (23 + z * (105 + z * (20 + z * (66 + z * (3 + z * (74 + z * (65 + z * (69 + z * (16 + z * (68 + z * (44 + z * (65 + z * (120 + z * (29 + z * (35 + z * 129)))))))))))))))))))

def pow11_138_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (4 + z * (26 + z * (112 + z * (50 + z * (36 + z * (125 + z * (38 + z * (111 + z * (68 + z * (40 + z * (37 + z * (130 + z * (42 + z * (13 + z * (60 + z * (66 + z * (117 + z * 47))))))))))))))))))

def pow11_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-95) + z * ((-113) + z * ((-128) + z * ((-211) + z * ((-173) + z * ((-89) + z * ((-87) + z * ((-27) + z * ((-91) + z * ((-85) + z * ((-155) + z * ((-43) + z * ((-119) + z * ((-246) + z * ((-146) + z * ((-203) + z * ((-187) + z * ((-86) + z * ((-91) + z * ((-197) + z * (24 + z * ((-133) + z * ((-70) + z * (160 + z * ((-120) + z * ((-232) + z * ((-75) + z * ((-143) + z * ((-110) + z * (90 + z * ((-13) + z * ((-161) + z * ((-20) + z * (35 + z * (34 + z * ((-80) + z * ((-114) + z * (21 + z * 38))))))))))))))))))))))))))))))))))))))

theorem pow11_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_69 z * pow11_69 z = pow11_138_q z * f z + pow11_138 z + (139 : R) * pow11_138_mul_t z := by
  simp only [pow11_69, pow11_138_q, f, pow11_138, pow11_138_mul_t]
  
  ring

theorem pow11_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_69 z * pow11_69 z = pow11_138_q z * f z + pow11_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_138_mul_integer z


theorem pow11_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_69 z * pow11_69 z = pow11_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_138_mul z


theorem pow11_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 138 = pow11_138 z := by
  calc
    _ = u10 z ^ 69 * u10 z ^ 69 := by ring
    _ = pow11_69 z * pow11_69 z := by rw [pow11_69_pow z hz]
    _ = _ := pow11_138_root z hz


def pow11_139 {R : Type*} [CommRing R] (z : R) : R := (95 + z * (69 + z * (130 + z * (13 + z * (126 + z * (81 + z * (93 + z * (54 + z * (134 + z * (105 + z * (113 + z * (46 + z * (118 + z * (14 + z * (133 + z * (102 + z * (114 + z * (62 + z * (81 + z * 92)))))))))))))))))))

def pow11_139_q {R : Type*} [CommRing R] (z : R) : R := (108 + z * (19 + z * (39 + z * (35 + z * (34 + z * (101 + z * (4 + z * (124 + z * (107 + z * (106 + z * (113 + z * (131 + z * (62 + z * (54 + z * (108 + z * (135 + z * (80 + z * (81 + z * 17))))))))))))))))))

def pow11_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-80) + z * ((-51) + z * (5 + z * ((-48) + z * ((-118) + z * ((-106) + z * ((-34) + z * ((-161) + z * ((-268) + z * ((-287) + z * ((-372) + z * ((-417) + z * ((-386) + z * ((-377) + z * ((-368) + z * ((-545) + z * ((-517) + z * ((-464) + z * ((-443) + z * ((-447) + z * ((-408) + z * ((-347) + z * ((-223) + z * ((-400) + z * ((-365) + z * ((-319) + z * ((-389) + z * ((-242) + z * ((-130) + z * ((-187) + z * ((-208) + z * ((-82) + z * (34 + z * ((-60) + z * ((-42) + z * (11 + z * (43 + z * (82 + z * 37))))))))))))))))))))))))))))))))))))))

theorem pow11_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_138 z * u10 z = pow11_139_q z * f z + pow11_139 z + (139 : R) * pow11_139_mul_t z := by
  simp only [pow11_138, u10, pow11_139_q, f, pow11_139, pow11_139_mul_t]
  simp only [pow10_139]
  ring

theorem pow11_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow11_138 z * u10 z = pow11_139_q z * f z + pow11_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow11_139_mul_integer z


theorem pow11_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow11_138 z * u10 z = pow11_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_139_mul z


theorem pow11_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u10 z ^ 139 = pow11_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow11_138_pow z hz]
  exact pow11_139_root z hz


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_139 z

theorem iterate11 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 11) = u11 z := by
  calc
    _ = (z ^ (139 ^ 10)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u10 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate10 z hz)
    _ = _ := pow11_139_pow z hz


def pow12_2 {R : Type*} [CommRing R] (z : R) : R := (73 + z * (114 + z * (65 + z * (30 + z * (73 + z * (91 + z * (4 + z * (73 + z * (10 + z * (31 + z * (32 + z * (88 + z * (98 + z * (14 + z * (48 + z * (87 + z * (100 + z * (80 + z * (15 + z * 41)))))))))))))))))))

def pow12_2_q {R : Type*} [CommRing R] (z : R) : R := (121 + z * (101 + z * (4 + z * (23 + z * (67 + z * (125 + z * (77 + z * (33 + z * (27 + z * (121 + z * (61 + z * (71 + z * (135 + z * (98 + z * (51 + z * (130 + z * (94 + z * (5 + z * 124))))))))))))))))))

def pow12_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-89) + z * (11 + z * ((-80) + z * (41 + z * ((-34) + z * (119 + z * ((-49) + z * (118 + z * (35 + z * (186 + z * (89 + z * (231 + z * ((-98) + z * (160 + z * ((-62) + z * (246 + z * (170 + z * (249 + z * (28 + z * (331 + z * (232 + z * (194 + z * (274 + z * (285 + z * (49 + z * (299 + z * (164 + z * (33 + z * (132 + z * (139 + z * ((-25) + z * (96 + z * (170 + z * (3 + z * (132 + z * (33 + z * ((-7) + z * 60))))))))))))))))))))))))))))))))))))))

theorem pow12_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z + (139 : R) * pow12_2_mul_t z := by
  simp only [u11, pow12_2_q, f, pow12_2, pow12_2_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_2_mul_integer z


theorem pow12_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z * u11 z = pow12_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_2_mul z


theorem pow12_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 2 = pow12_2 z := by
  calc
    _ = u11 z ^ 1 * u11 z ^ 1 := by ring
    _ = u11 z * u11 z := by simp only [pow_one]
    _ = _ := pow12_2_root z hz


def pow12_4 {R : Type*} [CommRing R] (z : R) : R := (58 + z * (66 + z * (131 + z * (66 + z * (43 + z * (80 + z * (8 + z * (46 + z * (137 + z * (91 + z * (93 + z * (9 + z * (8 + z * (22 + z * (133 + z * (40 + z * (22 + z * (29 + z * (81 + z * 45)))))))))))))))))))

def pow12_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (103 + z * (52 + z * (105 + z * (106 + z * (116 + z * (88 + z * (43 + z * (37 + z * (55 + z * (55 + z * (2 + z * (15 + z * (111 + z * (112 + z * (131 + z * (129 + z * (122 + z * 13))))))))))))))))))

def pow12_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-27) + z * ((-39) + z * ((-154) + z * ((-222) + z * ((-186) + z * ((-234) + z * ((-292) + z * ((-278) + z * ((-295) + z * ((-368) + z * ((-255) + z * ((-97) + z * ((-316) + z * ((-396) + z * ((-401) + z * ((-375) + z * ((-431) + z * ((-495) + z * ((-511) + z * ((-414) + z * ((-287) + z * ((-344) + z * ((-380) + z * ((-357) + z * ((-381) + z * ((-213) + z * ((-120) + z * ((-114) + z * ((-194) + z * ((-149) + z * ((-109) + z * ((-185) + z * ((-148) + z * ((-108) + z * ((-133) + z * ((-74) + z * ((-4) + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow12_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z + (139 : R) * pow12_4_mul_t z := by
  simp only [pow12_2, pow12_4_q, f, pow12_4, pow12_4_mul_t]
  
  ring

theorem pow12_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_4_mul_integer z


theorem pow12_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_2 z * pow12_2 z = pow12_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_4_mul z


theorem pow12_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 4 = pow12_4 z := by
  calc
    _ = u11 z ^ 2 * u11 z ^ 2 := by ring
    _ = pow12_2 z * pow12_2 z := by rw [pow12_2_pow z hz]
    _ = _ := pow12_4_root z hz


def pow12_8 {R : Type*} [CommRing R] (z : R) : R := (90 + z * (63 + z * (85 + z * (3 + z * (60 + z * (82 + z * (36 + z * (35 + z * (121 + z * (90 + z * (89 + z * (67 + z * (104 + z * (7 + z * (35 + z * (67 + z * (90 + z * (10 + z * (116 + z * 12)))))))))))))))))))

def pow12_8_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (111 + z * (71 + z * (107 + z * (14 + z * (76 + z * (130 + z * (72 + z * (101 + z * (72 + z * (89 + z * (39 + z * (26 + z * (10 + z * (20 + z * (53 + z * (95 + z * (97 + z * 79))))))))))))))))))

def pow12_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * ((-38) + z * ((-20) + z * ((-73) + z * ((-60) + z * ((-92) + z * ((-177) + z * ((-162) + z * ((-202) + z * ((-193) + z * ((-107) + z * ((-195) + z * ((-172) + z * ((-195) + z * ((-203) + z * ((-182) + z * ((-175) + z * ((-231) + z * ((-269) + z * ((-348) + z * ((-376) + z * ((-365) + z * ((-145) + z * ((-67) + z * ((-220) + z * ((-351) + z * ((-217) + z * ((-132) + z * ((-27) + z * ((-127) + z * ((-178) + z * ((-152) + z * ((-9) + z * ((-47) + z * ((-127) + z * ((-111) + z * ((-82) + z * ((-21) + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow12_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z + (139 : R) * pow12_8_mul_t z := by
  simp only [pow12_4, pow12_8_q, f, pow12_8, pow12_8_mul_t]
  
  ring

theorem pow12_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_4 z * pow12_4 z = pow12_8_q z * f z + pow12_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_8_mul_integer z


theorem pow12_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_4 z * pow12_4 z = pow12_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_8_mul z


theorem pow12_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 8 = pow12_8 z := by
  calc
    _ = u11 z ^ 4 * u11 z ^ 4 := by ring
    _ = pow12_4 z * pow12_4 z := by rw [pow12_4_pow z hz]
    _ = _ := pow12_8_root z hz


def pow12_16 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (20 + z * (20 + z * (114 + z * (103 + z * (19 + z * (88 + z * (41 + z * (34 + z * (18 + z * (14 + z * (11 + z * (96 + z * (67 + z * (5 + z * (120 + z * (105 + z * (55 + z * (88 + z * 87)))))))))))))))))))

def pow12_16_q {R : Type*} [CommRing R] (z : R) : R := (53 + z * (78 + z * (113 + z * (39 + z * (32 + z * (39 + z * (44 + z * (35 + z * (133 + z * (9 + z * (131 + z * (97 + z * (20 + z * (102 + z * (102 + z * (110 + z * (74 + z * (59 + z * 5))))))))))))))))))

def pow12_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * ((-24) + z * ((-63) + z * ((-169) + z * ((-144) + z * ((-113) + z * ((-70) + z * ((-71) + z * ((-95) + z * ((-61) + z * ((-95) + z * ((-246) + z * ((-108) + z * ((-144) + z * ((-232) + z * ((-359) + z * ((-193) + z * ((-311) + z * ((-225) + z * ((-198) + z * ((-102) + z * ((-282) + z * ((-81) + z * ((-170) + z * ((-176) + z * ((-143) + z * ((-127) + z * ((-92) + z * ((-45) + z * ((-288) + z * ((-84) + z * ((-141) + z * ((-143) + z * ((-97) + z * (2 + z * ((-80) + z * (40 + z * (15 + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow12_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z + (139 : R) * pow12_16_mul_t z := by
  simp only [pow12_8, pow12_16_q, f, pow12_16, pow12_16_mul_t]
  
  ring

theorem pow12_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_8 z * pow12_8 z = pow12_16_q z * f z + pow12_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_16_mul_integer z


theorem pow12_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_8 z * pow12_8 z = pow12_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_16_mul z


theorem pow12_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 16 = pow12_16 z := by
  calc
    _ = u11 z ^ 8 * u11 z ^ 8 := by ring
    _ = pow12_8 z * pow12_8 z := by rw [pow12_8_pow z hz]
    _ = _ := pow12_16_root z hz


def pow12_17 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (103 + z * (103 + z * (88 + z * (109 + z * (39 + z * (7 + z * (105 + z * (7 + z * (36 + z * (46 + z * (80 + z * (65 + z * (66 + z * (11 + z * (6 + z * (114 + z * (86 + z * (54 + z * 86)))))))))))))))))))

def pow12_17_q {R : Type*} [CommRing R] (z : R) : R := (97 + z * (32 + z * (121 + z * (29 + z * (41 + z * (11 + z * (3 + z * (0 + z * (117 + z * (27 + z * (102 + z * (24 + z * (48 + z * (110 + z * (46 + z * (56 + z * (129 + z * (49 + z * 81))))))))))))))))))

def pow12_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-51) + z * ((-80) + z * ((-153) + z * ((-140) + z * ((-95) + z * ((-30) + z * (14 + z * (64 + z * (84 + z * ((-44) + z * ((-113) + z * ((-116) + z * ((-28) + z * ((-79) + z * ((-23) + z * ((-72) + z * ((-95) + z * ((-65) + z * ((-106) + z * ((-6) + z * (77 + z * (89 + z * (181 + z * (83 + z * (119 + z * (103 + z * ((-84) + z * (88 + z * (10 + z * ((-18) + z * (143 + z * (65 + z * (12 + z * (136 + z * (87 + z * (57 + z * (21 + z * (34 + z * 57))))))))))))))))))))))))))))))))))))))

theorem pow12_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_16 z * u11 z = pow12_17_q z * f z + pow12_17 z + (139 : R) * pow12_17_mul_t z := by
  simp only [pow12_16, u11, pow12_17_q, f, pow12_17, pow12_17_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_16 z * u11 z = pow12_17_q z * f z + pow12_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_17_mul_integer z


theorem pow12_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_16 z * u11 z = pow12_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_17_mul z


theorem pow12_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 17 = pow12_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow12_16_pow z hz]
  exact pow12_17_root z hz


def pow12_34 {R : Type*} [CommRing R] (z : R) : R := (47 + z * (34 + z * (9 + z * (22 + z * (47 + z * (28 + z * (44 + z * (107 + z * (4 + z * (63 + z * (91 + z * (80 + z * (133 + z * (62 + z * (35 + z * (15 + z * (40 + z * (4 + z * (68 + z * 21)))))))))))))))))))

def pow12_34_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (93 + z * (132 + z * (4 + z * (85 + z * (105 + z * (135 + z * (51 + z * (102 + z * (14 + z * (70 + z * (12 + z * (87 + z * (15 + z * (116 + z * (47 + z * (53 + z * (16 + z * 29))))))))))))))))))

def pow12_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-74) + z * ((-111) + z * ((-148) + z * ((-107) + z * ((-95) + z * ((-76) + z * ((-166) + z * ((-205) + z * ((-266) + z * ((-349) + z * ((-394) + z * ((-232) + z * ((-243) + z * ((-211) + z * ((-255) + z * ((-461) + z * ((-414) + z * ((-275) + z * ((-255) + z * ((-178) + z * ((-64) + z * ((-161) + z * ((-136) + z * ((-70) + z * ((-246) + z * ((-215) + z * ((-56) + z * ((-108) + z * (8 + z * (69 + z * (3 + z * ((-43) + z * (25 + z * ((-14) + z * (42 + z * (147 + z * (91 + z * (40 + z * 53))))))))))))))))))))))))))))))))))))))

theorem pow12_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_17 z * pow12_17 z = pow12_34_q z * f z + pow12_34 z + (139 : R) * pow12_34_mul_t z := by
  simp only [pow12_17, pow12_34_q, f, pow12_34, pow12_34_mul_t]
  
  ring

theorem pow12_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_17 z * pow12_17 z = pow12_34_q z * f z + pow12_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_34_mul_integer z


theorem pow12_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_17 z * pow12_17 z = pow12_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_34_mul z


theorem pow12_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 34 = pow12_34 z := by
  calc
    _ = u11 z ^ 17 * u11 z ^ 17 := by ring
    _ = pow12_17 z * pow12_17 z := by rw [pow12_17_pow z hz]
    _ = _ := pow12_34_root z hz


def pow12_68 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (122 + z * (136 + z * (71 + z * (8 + z * (120 + z * (122 + z * (79 + z * (57 + z * (22 + z * (33 + z * (115 + z * (42 + z * (125 + z * (90 + z * (74 + z * (21 + z * (38 + z * (55 + z * 15)))))))))))))))))))

def pow12_68_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (31 + z * (127 + z * (99 + z * (113 + z * (71 + z * (123 + z * (53 + z * (62 + z * (68 + z * (73 + z * (42 + z * (5 + z * (71 + z * (128 + z * (135 + z * (107 + z * (62 + z * 24))))))))))))))))))

def pow12_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-25) + z * ((-134) + z * ((-221) + z * ((-294) + z * ((-351) + z * ((-417) + z * ((-349) + z * ((-381) + z * ((-414) + z * ((-395) + z * ((-385) + z * ((-383) + z * ((-361) + z * ((-398) + z * ((-585) + z * ((-558) + z * ((-613) + z * ((-601) + z * ((-461) + z * ((-481) + z * ((-412) + z * ((-334) + z * ((-319) + z * ((-364) + z * ((-263) + z * ((-280) + z * ((-259) + z * ((-198) + z * ((-260) + z * ((-165) + z * ((-175) + z * ((-233) + z * ((-257) + z * ((-180) + z * ((-129) + z * ((-41) + z * ((-2) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow12_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_34 z * pow12_34 z = pow12_68_q z * f z + pow12_68 z + (139 : R) * pow12_68_mul_t z := by
  simp only [pow12_34, pow12_68_q, f, pow12_68, pow12_68_mul_t]
  
  ring

theorem pow12_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_34 z * pow12_34 z = pow12_68_q z * f z + pow12_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_68_mul_integer z


theorem pow12_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_34 z * pow12_34 z = pow12_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_68_mul z


theorem pow12_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 68 = pow12_68 z := by
  calc
    _ = u11 z ^ 34 * u11 z ^ 34 := by ring
    _ = pow12_34 z * pow12_34 z := by rw [pow12_34_pow z hz]
    _ = _ := pow12_68_root z hz


def pow12_69 {R : Type*} [CommRing R] (z : R) : R := (41 + z * (9 + z * (20 + z * (51 + z * (25 + z * (81 + z * (54 + z * (86 + z * (137 + z * (107 + z * (84 + z * (19 + z * (85 + z * (45 + z * (124 + z * (17 + z * (56 + z * (58 + z * (56 + z * 7)))))))))))))))))))

def pow12_69_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (118 + z * (129 + z * (82 + z * (126 + z * (67 + z * (32 + z * (56 + z * (85 + z * (80 + z * (105 + z * (114 + z * (118 + z * (42 + z * (112 + z * (15 + z * (15 + z * (49 + z * 129))))))))))))))))))

def pow12_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (10 + z * ((-2) + z * ((-65) + z * ((-170) + z * ((-141) + z * ((-21) + z * (73 + z * (5 + z * (21 + z * ((-21) + z * ((-114) + z * ((-175) + z * ((-61) + z * ((-154) + z * (75 + z * (57 + z * (46 + z * ((-82) + z * (28 + z * ((-109) + z * ((-41) + z * ((-19) + z * (30 + z * ((-21) + z * (64 + z * ((-58) + z * ((-120) + z * ((-87) + z * (63 + z * ((-19) + z * ((-32) + z * (48 + z * ((-40) + z * (1 + z * (23 + z * ((-76) + z * ((-74) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow12_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_68 z * u11 z = pow12_69_q z * f z + pow12_69 z + (139 : R) * pow12_69_mul_t z := by
  simp only [pow12_68, u11, pow12_69_q, f, pow12_69, pow12_69_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_68 z * u11 z = pow12_69_q z * f z + pow12_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_69_mul_integer z


theorem pow12_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_68 z * u11 z = pow12_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_69_mul z


theorem pow12_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 69 = pow12_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow12_68_pow z hz]
  exact pow12_69_root z hz


def pow12_138 {R : Type*} [CommRing R] (z : R) : R := (91 + z * (134 + z * (13 + z * (115 + z * (89 + z * (118 + z * (108 + z * (87 + z * (92 + z * (25 + z * (33 + z * (81 + z * (39 + z * (64 + z * (136 + z * (20 + z * (41 + z * (3 + z * (50 + z * 18)))))))))))))))))))

def pow12_138_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (116 + z * (0 + z * (101 + z * (109 + z * (58 + z * (92 + z * (128 + z * (87 + z * (94 + z * (134 + z * (23 + z * (34 + z * (129 + z * (113 + z * (17 + z * (20 + z * (72 + z * 49))))))))))))))))))

def pow12_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-114) + z * ((-121) + z * ((-182) + z * ((-285) + z * ((-267) + z * ((-294) + z * ((-373) + z * ((-345) + z * ((-384) + z * ((-468) + z * ((-442) + z * ((-283) + z * ((-387) + z * ((-408) + z * ((-268) + z * ((-383) + z * ((-334) + z * ((-265) + z * ((-363) + z * ((-350) + z * ((-133) + z * ((-201) + z * ((-283) + z * ((-88) + z * ((-158) + z * ((-137) + z * ((-185) + z * ((-144) + z * ((-214) + z * ((-30) + z * ((-67) + z * ((-144) + z * ((-136) + z * ((-1) + z * ((-19) + z * ((-74) + z * ((-40) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow12_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_69 z * pow12_69 z = pow12_138_q z * f z + pow12_138 z + (139 : R) * pow12_138_mul_t z := by
  simp only [pow12_69, pow12_138_q, f, pow12_138, pow12_138_mul_t]
  
  ring

theorem pow12_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_69 z * pow12_69 z = pow12_138_q z * f z + pow12_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_138_mul_integer z


theorem pow12_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_69 z * pow12_69 z = pow12_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_138_mul z


theorem pow12_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 138 = pow12_138 z := by
  calc
    _ = u11 z ^ 69 * u11 z ^ 69 := by ring
    _ = pow12_69 z * pow12_69 z := by rw [pow12_69_pow z hz]
    _ = _ := pow12_138_root z hz


def pow12_139 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (52 + z * (119 + z * (45 + z * (122 + z * (2 + z * (134 + z * (26 + z * (82 + z * (45 + z * (43 + z * (55 + z * (119 + z * (30 + z * (71 + z * (36 + z * (7 + z * (90 + z * (135 + z * 30)))))))))))))))))))

def pow12_139_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (25 + z * (138 + z * (134 + z * (88 + z * (16 + z * (80 + z * (25 + z * (113 + z * (18 + z * (44 + z * (72 + z * (4 + z * (85 + z * (43 + z * (70 + z * (128 + z * (88 + z * 127))))))))))))))))))

def pow12_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (28 + z * (78 + z * ((-7) + z * ((-69) + z * ((-143) + z * (34 + z * ((-36) + z * (101 + z * (123 + z * (167 + z * (98 + z * (76 + z * (85 + z * (150 + z * (201 + z * (246 + z * (87 + z * ((-20) + z * ((-73) + z * (6 + z * (67 + z * ((-131) + z * (101 + z * (108 + z * (26 + z * ((-27) + z * ((-103) + z * ((-148) + z * (7 + z * ((-95) + z * (2 + z * ((-169) + z * ((-110) + z * ((-70) + z * ((-172) + z * ((-117) + z * ((-136) + z * ((-74) + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow12_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_138 z * u11 z = pow12_139_q z * f z + pow12_139 z + (139 : R) * pow12_139_mul_t z := by
  simp only [pow12_138, u11, pow12_139_q, f, pow12_139, pow12_139_mul_t]
  simp only [pow11_139]
  ring

theorem pow12_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow12_138 z * u11 z = pow12_139_q z * f z + pow12_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow12_139_mul_integer z


theorem pow12_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow12_138 z * u11 z = pow12_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_139_mul z


theorem pow12_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u11 z ^ 139 = pow12_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow12_138_pow z hz]
  exact pow12_139_root z hz


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_139 z

theorem iterate12 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 12) = u12 z := by
  calc
    _ = (z ^ (139 ^ 11)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate11 z hz)
    _ = _ := pow12_139_pow z hz

end DimensionTen.Mod139

end

end OAI
