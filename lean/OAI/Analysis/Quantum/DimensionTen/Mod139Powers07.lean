import OAI.Analysis.Quantum.DimensionTen.Mod139Powers06

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow13_2 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (63 + z * (29 + z * (18 + z * (98 + z * (30 + z * (65 + z * (74 + z * (51 + z * (19 + z * (59 + z * (134 + z * (23 + z * (100 + z * (85 + z * (115 + z * (108 + z * (88 + z * (16 + z * 103)))))))))))))))))))

def pow13_2_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (69 + z * (48 + z * (32 + z * (73 + z * (43 + z * (60 + z * (57 + z * (63 + z * (16 + z * (44 + z * (44 + z * (102 + z * (135 + z * (68 + z * (18 + z * (138 + z * (69 + z * 66))))))))))))))))))

def pow13_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-72) + z * ((-71) + z * ((-65) + z * ((-44) + z * ((-70) + z * (25 + z * ((-100) + z * (50 + z * ((-133) + z * (51 + z * ((-168) + z * (42 + z * ((-192) + z * ((-111) + z * ((-222) + z * ((-201) + z * ((-363) + z * ((-100) + z * ((-204) + z * ((-97) + z * ((-108) + z * ((-131) + z * ((-155) + z * (14 + z * ((-163) + z * ((-195) + z * ((-175) + z * ((-140) + z * ((-78) + z * ((-12) + z * ((-182) + z * ((-164) + z * ((-67) + z * ((-86) + z * (0 + z * (57 + z * ((-3) + z * 6))))))))))))))))))))))))))))))))))))))

theorem pow13_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z + (139 : R) * pow13_2_mul_t z := by
  simp only [u12, pow13_2_q, f, pow13_2, pow13_2_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_2_mul_integer z


theorem pow13_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z * u12 z = pow13_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_2_mul z


theorem pow13_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 2 = pow13_2 z := by
  calc
    _ = u12 z ^ 1 * u12 z ^ 1 := by ring
    _ = u12 z * u12 z := by simp only [pow_one]
    _ = _ := pow13_2_root z hz


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (32 + z * (10 + z * (38 + z * (11 + z * (55 + z * (24 + z * (124 + z * (78 + z * (17 + z * (64 + z * (121 + z * (32 + z * (133 + z * (120 + z * (2 + z * (133 + z * (25 + z * (4 + z * 117)))))))))))))))))))

def pow13_4_q {R : Type*} [CommRing R] (z : R) : R := (108 + z * (117 + z * (76 + z * (120 + z * (124 + z * (32 + z * (31 + z * (78 + z * (67 + z * (31 + z * (105 + z * (15 + z * (11 + z * (74 + z * (118 + z * (17 + z * (34 + z * (38 + z * 45))))))))))))))))))

def pow13_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * ((-71) + z * ((-177) + z * ((-307) + z * ((-266) + z * ((-288) + z * ((-223) + z * ((-222) + z * ((-201) + z * ((-316) + z * ((-372) + z * ((-171) + z * ((-223) + z * ((-268) + z * ((-238) + z * ((-16) + z * ((-223) + z * ((-111) + z * ((-162) + z * ((-63) + z * ((-120) + z * (58 + z * ((-23) + z * ((-6) + z * (141 + z * (170 + z * (143 + z * (190 + z * (176 + z * (140 + z * (365 + z * (185 + z * (171 + z * (107 + z * (172 + z * (121 + z * (64 + z * ((-18) + z * 76))))))))))))))))))))))))))))))))))))))

theorem pow13_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z + (139 : R) * pow13_4_mul_t z := by
  simp only [pow13_2, pow13_4_q, f, pow13_4, pow13_4_mul_t]
  
  ring

theorem pow13_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_4_mul_integer z


theorem pow13_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_2 z * pow13_2 z = pow13_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_4_mul z


theorem pow13_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 4 = pow13_4 z := by
  calc
    _ = u12 z ^ 2 * u12 z ^ 2 := by ring
    _ = pow13_2 z * pow13_2 z := by rw [pow13_2_pow z hz]
    _ = _ := pow13_4_root z hz


def pow13_8 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (34 + z * (116 + z * (112 + z * (84 + z * (73 + z * (123 + z * (87 + z * (29 + z * (66 + z * (56 + z * (123 + z * (128 + z * (11 + z * (83 + z * (73 + z * (110 + z * (88 + z * (125 + z * 50)))))))))))))))))))

def pow13_8_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (77 + z * (26 + z * (84 + z * (100 + z * (124 + z * (95 + z * (48 + z * (63 + z * (107 + z * (57 + z * (55 + z * (58 + z * (22 + z * (23 + z * (58 + z * (60 + z * (5 + z * 67))))))))))))))))))

def pow13_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-75) + z * ((-143) + z * ((-169) + z * ((-243) + z * ((-305) + z * ((-358) + z * ((-390) + z * ((-448) + z * ((-407) + z * ((-492) + z * ((-493) + z * ((-458) + z * ((-415) + z * ((-514) + z * ((-361) + z * ((-357) + z * ((-425) + z * ((-288) + z * ((-308) + z * ((-409) + z * ((-198) + z * (9 + z * ((-173) + z * ((-40) + z * (106 + z * ((-105) + z * (190 + z * (277 + z * ((-104) + z * (161 + z * (287 + z * ((-113) + z * (240 + z * (139 + z * ((-138) + z * (166 + z * ((-12) + z * ((-55) + z * 98))))))))))))))))))))))))))))))))))))))

theorem pow13_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z + (139 : R) * pow13_8_mul_t z := by
  simp only [pow13_4, pow13_8_q, f, pow13_8, pow13_8_mul_t]
  
  ring

theorem pow13_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_4 z * pow13_4 z = pow13_8_q z * f z + pow13_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_8_mul_integer z


theorem pow13_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_4 z * pow13_4 z = pow13_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_8_mul z


theorem pow13_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 8 = pow13_8 z := by
  calc
    _ = u12 z ^ 4 * u12 z ^ 4 := by ring
    _ = pow13_4 z * pow13_4 z := by rw [pow13_4_pow z hz]
    _ = _ := pow13_8_root z hz


def pow13_16 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (6 + z * (18 + z * (29 + z * (98 + z * (28 + z * (100 + z * (50 + z * (73 + z * (55 + z * (7 + z * (16 + z * (25 + z * (2 + z * (98 + z * (42 + z * (129 + z * (65 + z * (36 + z * 38)))))))))))))))))))

def pow13_16_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (89 + z * (32 + z * (130 + z * (22 + z * (101 + z * (115 + z * (85 + z * (126 + z * (39 + z * (47 + z * (105 + z * (138 + z * (91 + z * (138 + z * (13 + z * (91 + z * (107 + z * 137))))))))))))))))))

def pow13_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-43) + z * ((-5) + z * ((-64) + z * ((-29) + z * ((-28) + z * ((-9) + z * ((-35) + z * ((-49) + z * ((-29) + z * ((-109) + z * ((-96) + z * ((-75) + z * ((-94) + z * ((-116) + z * ((-191) + z * ((-197) + z * ((-70) + z * (11 + z * ((-105) + z * ((-29) + z * ((-86) + z * ((-12) + z * (123 + z * ((-80) + z * ((-72) + z * ((-145) + z * ((-181) + z * (73 + z * (96 + z * (9 + z * ((-104) + z * ((-51) + z * (16 + z * (112 + z * (75 + z * ((-24) + z * ((-37) + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow13_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z + (139 : R) * pow13_16_mul_t z := by
  simp only [pow13_8, pow13_16_q, f, pow13_16, pow13_16_mul_t]
  
  ring

theorem pow13_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_8 z * pow13_8 z = pow13_16_q z * f z + pow13_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_16_mul_integer z


theorem pow13_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_8 z * pow13_8 z = pow13_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_16_mul z


theorem pow13_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 16 = pow13_16 z := by
  calc
    _ = u12 z ^ 8 * u12 z ^ 8 := by ring
    _ = pow13_8 z * pow13_8 z := by rw [pow13_8_pow z hz]
    _ = _ := pow13_16_root z hz


def pow13_17 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (75 + z * (42 + z * (62 + z * (21 + z * (42 + z * (65 + z * (55 + z * (5 + z * (123 + z * (12 + z * (131 + z * (38 + z * (19 + z * (8 + z * (95 + z * (115 + z * (11 + z * (39 + z * 106)))))))))))))))))))

def pow13_17_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (16 + z * (53 + z * (31 + z * (82 + z * (115 + z * (34 + z * (101 + z * (110 + z * (135 + z * (12 + z * (25 + z * (111 + z * (95 + z * (48 + z * (97 + z * (120 + z * (124 + z * 28))))))))))))))))))

def pow13_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-33) + z * ((-38) + z * ((-96) + z * ((-86) + z * ((-187) + z * ((-89) + z * ((-216) + z * ((-169) + z * ((-336) + z * ((-203) + z * ((-302) + z * ((-243) + z * ((-401) + z * ((-347) + z * ((-458) + z * ((-446) + z * ((-528) + z * ((-401) + z * ((-502) + z * ((-300) + z * ((-373) + z * ((-292) + z * ((-354) + z * ((-312) + z * ((-345) + z * ((-283) + z * ((-329) + z * ((-233) + z * ((-140) + z * ((-209) + z * ((-228) + z * ((-142) + z * ((-60) + z * ((-13) + z * ((-86) + z * ((-62) + z * (18 + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow13_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_16 z * u12 z = pow13_17_q z * f z + pow13_17 z + (139 : R) * pow13_17_mul_t z := by
  simp only [pow13_16, u12, pow13_17_q, f, pow13_17, pow13_17_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_16 z * u12 z = pow13_17_q z * f z + pow13_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_17_mul_integer z


theorem pow13_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_16 z * u12 z = pow13_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_17_mul z


theorem pow13_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 17 = pow13_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow13_16_pow z hz]
  exact pow13_17_root z hz


def pow13_34 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (23 + z * (53 + z * (102 + z * (63 + z * (110 + z * (132 + z * (88 + z * (63 + z * (84 + z * (108 + z * (28 + z * (79 + z * (25 + z * (35 + z * (63 + z * (47 + z * (0 + z * (47 + z * 108)))))))))))))))))))

def pow13_34_q {R : Type*} [CommRing R] (z : R) : R := (79 + z * (34 + z * (3 + z * (91 + z * (115 + z * (93 + z * (117 + z * (36 + z * (119 + z * (111 + z * (52 + z * (60 + z * (119 + z * (111 + z * (111 + z * (99 + z * (122 + z * (92 + z * 116))))))))))))))))))

def pow13_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-79) + z * ((-54) + z * ((-119) + z * ((-180) + z * ((-238) + z * ((-301) + z * ((-325) + z * ((-357) + z * ((-424) + z * ((-377) + z * ((-392) + z * ((-332) + z * ((-588) + z * ((-558) + z * ((-639) + z * ((-662) + z * ((-607) + z * ((-661) + z * ((-848) + z * ((-414) + z * ((-567) + z * ((-498) + z * ((-558) + z * ((-494) + z * ((-390) + z * ((-357) + z * ((-359) + z * ((-310) + z * ((-320) + z * ((-162) + z * ((-272) + z * ((-250) + z * ((-243) + z * ((-68) + z * (1 + z * ((-143) + z * ((-48) + z * 80))))))))))))))))))))))))))))))))))))))

theorem pow13_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_17 z * pow13_17 z = pow13_34_q z * f z + pow13_34 z + (139 : R) * pow13_34_mul_t z := by
  simp only [pow13_17, pow13_34_q, f, pow13_34, pow13_34_mul_t]
  
  ring

theorem pow13_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_17 z * pow13_17 z = pow13_34_q z * f z + pow13_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_34_mul_integer z


theorem pow13_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_17 z * pow13_17 z = pow13_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_34_mul z


theorem pow13_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 34 = pow13_34 z := by
  calc
    _ = u12 z ^ 17 * u12 z ^ 17 := by ring
    _ = pow13_17 z * pow13_17 z := by rw [pow13_17_pow z hz]
    _ = _ := pow13_34_root z hz


def pow13_68 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (3 + z * (106 + z * (105 + z * (11 + z * (55 + z * (52 + z * (136 + z * (96 + z * (126 + z * (16 + z * (88 + z * (47 + z * (96 + z * (56 + z * (8 + z * (38 + z * (134 + z * (104 + z * 17)))))))))))))))))))

def pow13_68_q {R : Type*} [CommRing R] (z : R) : R := (129 + z * (20 + z * (117 + z * (21 + z * (62 + z * (47 + z * (35 + z * (115 + z * (131 + z * (115 + z * (96 + z * (27 + z * (69 + z * (78 + z * (74 + z * (49 + z * (90 + z * (12 + z * 127))))))))))))))))))

def pow13_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (26 + z * ((-85) + z * ((-119) + z * ((-50) + z * ((-118) + z * (31 + z * (122 + z * (36 + z * ((-17) + z * ((-49) + z * ((-69) + z * ((-111) + z * (35 + z * ((-80) + z * ((-76) + z * ((-59) + z * ((-203) + z * ((-286) + z * ((-323) + z * ((-140) + z * ((-301) + z * ((-198) + z * ((-137) + z * ((-289) + z * ((-79) + z * ((-126) + z * ((-278) + z * ((-269) + z * ((-222) + z * ((-122) + z * ((-100) + z * ((-161) + z * ((-184) + z * ((-99) + z * ((-88) + z * ((-19) + z * ((-89) + z * ((-44) + z * 83))))))))))))))))))))))))))))))))))))))

theorem pow13_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_34 z * pow13_34 z = pow13_68_q z * f z + pow13_68 z + (139 : R) * pow13_68_mul_t z := by
  simp only [pow13_34, pow13_68_q, f, pow13_68, pow13_68_mul_t]
  
  ring

theorem pow13_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_34 z * pow13_34 z = pow13_68_q z * f z + pow13_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_68_mul_integer z


theorem pow13_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_34 z * pow13_34 z = pow13_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_68_mul z


theorem pow13_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 68 = pow13_68 z := by
  calc
    _ = u12 z ^ 34 * u12 z ^ 34 := by ring
    _ = pow13_34 z * pow13_34 z := by rw [pow13_34_pow z hz]
    _ = _ := pow13_68_root z hz


def pow13_69 {R : Type*} [CommRing R] (z : R) : R := (80 + z * (82 + z * (71 + z * (12 + z * (64 + z * (86 + z * (117 + z * (10 + z * (104 + z * (98 + z * (38 + z * (83 + z * (114 + z * (132 + z * (67 + z * (112 + z * (80 + z * (131 + z * (103 + z * 25)))))))))))))))))))

def pow13_69_q {R : Type*} [CommRing R] (z : R) : R := (107 + z * (111 + z * (98 + z * (137 + z * (13 + z * (27 + z * (9 + z * (130 + z * (16 + z * (124 + z * (114 + z * (8 + z * (52 + z * (52 + z * (66 + z * (21 + z * (24 + z * (44 + z * 93))))))))))))))))))

def pow13_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-81) + z * ((-177) + z * ((-244) + z * ((-327) + z * ((-273) + z * ((-226) + z * ((-151) + z * ((-183) + z * ((-120) + z * ((-148) + z * ((-366) + z * ((-212) + z * ((-289) + z * ((-179) + z * ((-163) + z * ((-43) + z * ((-368) + z * ((-164) + z * ((-286) + z * ((-160) + z * ((-30) + z * (36 + z * ((-171) + z * ((-11) + z * (105 + z * (28 + z * (7 + z * ((-25) + z * ((-148) + z * (52 + z * (87 + z * (31 + z * ((-10) + z * ((-86) + z * (20 + z * (152 + z * (32 + z * ((-47) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow13_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_68 z * u12 z = pow13_69_q z * f z + pow13_69 z + (139 : R) * pow13_69_mul_t z := by
  simp only [pow13_68, u12, pow13_69_q, f, pow13_69, pow13_69_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_68 z * u12 z = pow13_69_q z * f z + pow13_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_69_mul_integer z


theorem pow13_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_68 z * u12 z = pow13_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_69_mul z


theorem pow13_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 69 = pow13_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow13_68_pow z hz]
  exact pow13_69_root z hz


def pow13_138 {R : Type*} [CommRing R] (z : R) : R := (86 + z * (73 + z * (96 + z * (47 + z * (117 + z * (101 + z * (125 + z * (61 + z * (73 + z * (134 + z * (50 + z * (120 + z * (9 + z * (65 + z * (31 + z * (59 + z * (87 + z * (112 + z * (58 + z * 1)))))))))))))))))))

def pow13_138_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (28 + z * (125 + z * (120 + z * (29 + z * (44 + z * (113 + z * (37 + z * (24 + z * (62 + z * (135 + z * (137 + z * (121 + z * (128 + z * (132 + z * (79 + z * (60 + z * (71 + z * 69))))))))))))))))))

def pow13_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-49) + z * ((-37) + z * ((-102) + z * ((-247) + z * ((-241) + z * ((-159) + z * ((-112) + z * ((-157) + z * ((-87) + z * ((-141) + z * ((-180) + z * ((-213) + z * ((-272) + z * ((-291) + z * ((-174) + z * ((-328) + z * ((-353) + z * (55 + z * ((-89) + z * ((-140) + z * ((-107) + z * ((-80) + z * ((-14) + z * (173 + z * (69 + z * (16 + z * (124 + z * (63 + z * (58 + z * (73 + z * (130 + z * (87 + z * (64 + z * (57 + z * (107 + z * (115 + z * (7 + z * ((-27) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow13_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_69 z * pow13_69 z = pow13_138_q z * f z + pow13_138 z + (139 : R) * pow13_138_mul_t z := by
  simp only [pow13_69, pow13_138_q, f, pow13_138, pow13_138_mul_t]
  
  ring

theorem pow13_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_69 z * pow13_69 z = pow13_138_q z * f z + pow13_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_138_mul_integer z


theorem pow13_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_69 z * pow13_69 z = pow13_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_138_mul z


theorem pow13_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 138 = pow13_138 z := by
  calc
    _ = u12 z ^ 69 * u12 z ^ 69 := by ring
    _ = pow13_69 z * pow13_69 z := by rw [pow13_69_pow z hz]
    _ = _ := pow13_138_root z hz


def pow13_139 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (85 + z * (128 + z * (125 + z * (89 + z * (72 + z * (18 + z * (116 + z * (63 + z * (21 + z * (127 + z * (70 + z * (15 + z * (52 + z * (25 + z * (92 + z * (4 + z * (74 + z * (10 + z * 128)))))))))))))))))))

def pow13_139_q {R : Type*} [CommRing R] (z : R) : R := (136 + z * (74 + z * (65 + z * (106 + z * (121 + z * (111 + z * (44 + z * (75 + z * (67 + z * (118 + z * (124 + z * (107 + z * (36 + z * (119 + z * (4 + z * (9 + z * (88 + z * (120 + z * 30))))))))))))))))))

def pow13_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-86) + z * ((-129) + z * ((-117) + z * ((-198) + z * ((-198) + z * ((-246) + z * ((-114) + z * ((-202) + z * ((-91) + z * ((-240) + z * ((-249) + z * ((-284) + z * ((-215) + z * ((-361) + z * ((-335) + z * ((-166) + z * ((-352) + z * ((-196) + z * ((-304) + z * ((-301) + z * ((-304) + z * ((-145) + z * ((-141) + z * ((-120) + z * ((-129) + z * ((-142) + z * ((-255) + z * ((-114) + z * ((-56) + z * ((-105) + z * ((-79) + z * ((-82) + z * ((-130) + z * (11 + z * (75 + z * ((-4) + z * ((-52) + z * ((-15) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow13_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_138 z * u12 z = pow13_139_q z * f z + pow13_139 z + (139 : R) * pow13_139_mul_t z := by
  simp only [pow13_138, u12, pow13_139_q, f, pow13_139, pow13_139_mul_t]
  simp only [pow12_139]
  ring

theorem pow13_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow13_138 z * u12 z = pow13_139_q z * f z + pow13_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow13_139_mul_integer z


theorem pow13_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow13_138 z * u12 z = pow13_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_139_mul z


theorem pow13_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u12 z ^ 139 = pow13_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow13_138_pow z hz]
  exact pow13_139_root z hz


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_139 z

theorem iterate13 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 13) = u13 z := by
  calc
    _ = (z ^ (139 ^ 12)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate12 z hz)
    _ = _ := pow13_139_pow z hz


def pow14_2 {R : Type*} [CommRing R] (z : R) : R := (79 + z * (97 + z * (110 + z * (22 + z * (128 + z * (72 + z * (91 + z * (9 + z * (128 + z * (69 + z * (108 + z * (52 + z * (118 + z * (4 + z * (129 + z * (89 + z * (9 + z * (118 + z * (59 + z * 70)))))))))))))))))))

def pow14_2_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (81 + z * (137 + z * (41 + z * (131 + z * (29 + z * (101 + z * (99 + z * (104 + z * (105 + z * (73 + z * (85 + z * (4 + z * (9 + z * (36 + z * (35 + z * (19 + z * (138 + z * 121))))))))))))))))))

def pow14_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-52) + z * ((-65) + z * ((-18) + z * ((-41) + z * (25 + z * ((-41) + z * ((-21) + z * ((-114) + z * ((-202) + z * ((-178) + z * ((-198) + z * ((-114) + z * ((-116) + z * ((-127) + z * ((-97) + z * ((-267) + z * ((-197) + z * ((-320) + z * ((-341) + z * ((-264) + z * ((-181) + z * ((-80) + z * ((-178) + z * ((-173) + z * ((-222) + z * ((-145) + z * ((-239) + z * ((-156) + z * (42 + z * ((-52) + z * ((-156) + z * (8 + z * ((-188) + z * (62 + z * ((-101) + z * ((-79) + z * ((-94) + z * 117))))))))))))))))))))))))))))))))))))))

theorem pow14_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z + (139 : R) * pow14_2_mul_t z := by
  simp only [u13, pow14_2_q, f, pow14_2, pow14_2_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_2_mul_integer z


theorem pow14_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z * u13 z = pow14_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_2_mul z


theorem pow14_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 2 = pow14_2 z := by
  calc
    _ = u13 z ^ 1 * u13 z ^ 1 := by ring
    _ = u13 z * u13 z := by simp only [pow_one]
    _ = _ := pow14_2_root z hz


def pow14_4 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (107 + z * (46 + z * (82 + z * (86 + z * (103 + z * (89 + z * (67 + z * (30 + z * (105 + z * (115 + z * (41 + z * (36 + z * (80 + z * (114 + z * (31 + z * (12 + z * (67 + z * (44 + z * 135)))))))))))))))))))

def pow14_4_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (90 + z * (115 + z * (103 + z * (71 + z * (35 + z * (73 + z * (63 + z * (44 + z * (89 + z * (20 + z * (18 + z * (13 + z * (41 + z * (66 + z * (31 + z * (48 + z * (27 + z * 35))))))))))))))))))

def pow14_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-41) + z * ((-58) + z * ((-171) + z * ((-144) + z * ((-95) + z * (12 + z * ((-118) + z * (26 + z * ((-79) + z * (53 + z * ((-71) + z * (194 + z * (17 + z * (271 + z * (55 + z * (190 + z * (28 + z * (253 + z * (199 + z * (298 + z * (175 + z * (207 + z * (336 + z * (211 + z * (216 + z * (259 + z * (253 + z * (147 + z * (338 + z * (78 + z * (210 + z * (107 + z * (92 + z * (104 + z * (45 + z * (93 + z * (27 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow14_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z + (139 : R) * pow14_4_mul_t z := by
  simp only [pow14_2, pow14_4_q, f, pow14_4, pow14_4_mul_t]
  
  ring

theorem pow14_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_4_mul_integer z


theorem pow14_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_2 z * pow14_2 z = pow14_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_4_mul z


theorem pow14_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 4 = pow14_4 z := by
  calc
    _ = u13 z ^ 2 * u13 z ^ 2 := by ring
    _ = pow14_2 z * pow14_2 z := by rw [pow14_2_pow z hz]
    _ = _ := pow14_4_root z hz


def pow14_8 {R : Type*} [CommRing R] (z : R) : R := (115 + z * (81 + z * (35 + z * (90 + z * (23 + z * (22 + z * (127 + z * (49 + z * (101 + z * (45 + z * (107 + z * (101 + z * (49 + z * (65 + z * (75 + z * (118 + z * (137 + z * (81 + z * (89 + z * 83)))))))))))))))))))

def pow14_8_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (33 + z * (30 + z * (81 + z * (90 + z * (50 + z * (21 + z * (110 + z * (34 + z * (104 + z * (30 + z * (62 + z * (116 + z * (59 + z * (9 + z * (43 + z * (56 + z * (102 + z * 16))))))))))))))))))

def pow14_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (69 + z * (118 + z * (64 + z * (48 + z * (55 + z * (110 + z * (152 + z * (80 + z * (47 + z * (107 + z * (197 + z * (95 + z * ((-12) + z * ((-1) + z * (196 + z * (149 + z * ((-45) + z * ((-16) + z * (38 + z * (186 + z * (118 + z * ((-29) + z * ((-17) + z * (162 + z * (210 + z * ((-91) + z * ((-64) + z * ((-14) + z * (103 + z * (121 + z * ((-94) + z * ((-44) + z * (78 + z * (117 + z * (6 + z * ((-61) + z * (38 + z * (70 + z * 131))))))))))))))))))))))))))))))))))))))

theorem pow14_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z + (139 : R) * pow14_8_mul_t z := by
  simp only [pow14_4, pow14_8_q, f, pow14_8, pow14_8_mul_t]
  
  ring

theorem pow14_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_4 z * pow14_4 z = pow14_8_q z * f z + pow14_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_8_mul_integer z


theorem pow14_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_4 z * pow14_4 z = pow14_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_8_mul z


theorem pow14_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 8 = pow14_8 z := by
  calc
    _ = u13 z ^ 4 * u13 z ^ 4 := by ring
    _ = pow14_4 z * pow14_4 z := by rw [pow14_4_pow z hz]
    _ = _ := pow14_8_root z hz


def pow14_16 {R : Type*} [CommRing R] (z : R) : R := (58 + z * (4 + z * (95 + z * (33 + z * (31 + z * (24 + z * (122 + z * (41 + z * (8 + z * (123 + z * (92 + z * (65 + z * (131 + z * (91 + z * (138 + z * (99 + z * (91 + z * (111 + z * (111 + z * 1)))))))))))))))))))

def pow14_16_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (118 + z * (110 + z * (33 + z * (30 + z * (124 + z * (36 + z * (127 + z * (76 + z * (9 + z * (71 + z * (89 + z * (106 + z * (7 + z * (135 + z * (54 + z * (76 + z * (64 + z * 78))))))))))))))))))

def pow14_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (63 + z * (8 + z * ((-120) + z * ((-78) + z * ((-144) + z * ((-251) + z * ((-26) + z * ((-121) + z * ((-159) + z * ((-115) + z * ((-160) + z * ((-116) + z * ((-124) + z * ((-70) + z * ((-155) + z * ((-221) + z * (53 + z * ((-31) + z * ((-21) + z * (124 + z * ((-180) + z * ((-40) + z * (232 + z * (62 + z * (115 + z * (212 + z * (148 + z * (147 + z * (186 + z * (220 + z * (89 + z * (165 + z * (203 + z * (133 + z * (192 + z * (150 + z * (37 + z * (34 + z * 49))))))))))))))))))))))))))))))))))))))

theorem pow14_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z + (139 : R) * pow14_16_mul_t z := by
  simp only [pow14_8, pow14_16_q, f, pow14_16, pow14_16_mul_t]
  
  ring

theorem pow14_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_8 z * pow14_8 z = pow14_16_q z * f z + pow14_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_16_mul_integer z


theorem pow14_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_8 z * pow14_8 z = pow14_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_16_mul z


theorem pow14_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 16 = pow14_16 z := by
  calc
    _ = u13 z ^ 8 * u13 z ^ 8 := by ring
    _ = pow14_8 z * pow14_8 z := by rw [pow14_8_pow z hz]
    _ = _ := pow14_16_root z hz


def pow14_17 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (104 + z * (80 + z * (56 + z * (33 + z * (123 + z * (35 + z * (99 + z * (118 + z * (70 + z * (53 + z * (15 + z * (84 + z * (16 + z * (24 + z * (26 + z * (1 + z * (19 + z * (6 + z * 98)))))))))))))))))))

def pow14_17_q {R : Type*} [CommRing R] (z : R) : R := (129 + z * (66 + z * (72 + z * (37 + z * (72 + z * (61 + z * (75 + z * (44 + z * (101 + z * (103 + z * (113 + z * (41 + z * (120 + z * (96 + z * (22 + z * (97 + z * (55 + z * (58 + z * 128))))))))))))))))))

def pow14_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-64) + z * ((-126) + z * ((-117) + z * ((-140) + z * ((-149) + z * ((-121) + z * ((-116) + z * ((-100) + z * ((-200) + z * ((-197) + z * ((-262) + z * ((-217) + z * ((-179) + z * ((-193) + z * ((-133) + z * ((-193) + z * ((-128) + z * (26 + z * ((-284) + z * ((-145) + z * ((-146) + z * ((-57) + z * ((-170) + z * ((-126) + z * ((-85) + z * ((-92) + z * ((-155) + z * ((-146) + z * ((-144) + z * (10 + z * ((-58) + z * ((-116) + z * (1 + z * (37 + z * ((-76) + z * (57 + z * ((-37) + z * ((-16) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow14_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_16 z * u13 z = pow14_17_q z * f z + pow14_17 z + (139 : R) * pow14_17_mul_t z := by
  simp only [pow14_16, u13, pow14_17_q, f, pow14_17, pow14_17_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_16 z * u13 z = pow14_17_q z * f z + pow14_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_17_mul_integer z


theorem pow14_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_16 z * u13 z = pow14_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_17_mul z


theorem pow14_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 17 = pow14_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow14_16_pow z hz]
  exact pow14_17_root z hz


def pow14_34 {R : Type*} [CommRing R] (z : R) : R := (43 + z * (118 + z * (20 + z * (29 + z * (12 + z * (14 + z * (3 + z * (74 + z * (55 + z * (49 + z * (124 + z * (62 + z * (10 + z * (38 + z * (101 + z * (102 + z * (5 + z * (64 + z * (69 + z * 108)))))))))))))))))))

def pow14_34_q {R : Type*} [CommRing R] (z : R) : R := (57 + z * (44 + z * (131 + z * (8 + z * (93 + z * (122 + z * (84 + z * (102 + z * (99 + z * (14 + z * (65 + z * (137 + z * (122 + z * (20 + z * (15 + z * (134 + z * (124 + z * (68 + z * 13))))))))))))))))))

def pow14_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (39 + z * (76 + z * (12 + z * ((-9) + z * ((-101) + z * ((-54) + z * ((-99) + z * ((-69) + z * ((-56) + z * ((-57) + z * ((-27) + z * ((-252) + z * ((-191) + z * ((-177) + z * ((-308) + z * ((-418) + z * ((-450) + z * ((-445) + z * ((-654) + z * ((-405) + z * ((-502) + z * ((-544) + z * ((-330) + z * ((-488) + z * ((-393) + z * ((-533) + z * ((-393) + z * ((-231) + z * ((-247) + z * ((-270) + z * ((-395) + z * ((-233) + z * ((-151) + z * ((-141) + z * ((-186) + z * ((-162) + z * ((-46) + z * ((-4) + z * 69))))))))))))))))))))))))))))))))))))))

theorem pow14_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_17 z * pow14_17 z = pow14_34_q z * f z + pow14_34 z + (139 : R) * pow14_34_mul_t z := by
  simp only [pow14_17, pow14_34_q, f, pow14_34, pow14_34_mul_t]
  
  ring

theorem pow14_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_17 z * pow14_17 z = pow14_34_q z * f z + pow14_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_34_mul_integer z


theorem pow14_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_17 z * pow14_17 z = pow14_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_34_mul z


theorem pow14_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 34 = pow14_34 z := by
  calc
    _ = u13 z ^ 17 * u13 z ^ 17 := by ring
    _ = pow14_17 z * pow14_17 z := by rw [pow14_17_pow z hz]
    _ = _ := pow14_34_root z hz


def pow14_68 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (86 + z * (79 + z * (46 + z * (57 + z * (41 + z * (135 + z * (28 + z * (103 + z * (104 + z * (40 + z * (10 + z * (9 + z * (108 + z * (101 + z * (80 + z * (6 + z * (29 + z * (15 + z * 26)))))))))))))))))))

def pow14_68_q {R : Type*} [CommRing R] (z : R) : R := (61 + z * (111 + z * (83 + z * (41 + z * (48 + z * (54 + z * (41 + z * (89 + z * (45 + z * (37 + z * (1 + z * (79 + z * (35 + z * (53 + z * (64 + z * (17 + z * (72 + z * (38 + z * 127))))))))))))))))))

def pow14_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-65) + z * ((-103) + z * ((-210) + z * ((-241) + z * ((-267) + z * ((-246) + z * ((-267) + z * ((-208) + z * ((-270) + z * ((-239) + z * ((-181) + z * ((-229) + z * ((-321) + z * ((-325) + z * ((-226) + z * ((-295) + z * ((-323) + z * ((-247) + z * ((-270) + z * ((-251) + z * ((-286) + z * ((-166) + z * ((-169) + z * ((-35) + z * (12 + z * ((-85) + z * ((-83) + z * (95 + z * (158 + z * ((-36) + z * ((-113) + z * (20 + z * (78 + z * (18 + z * ((-23) + z * (5 + z * ((-10) + z * 83))))))))))))))))))))))))))))))))))))))

theorem pow14_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_34 z * pow14_34 z = pow14_68_q z * f z + pow14_68 z + (139 : R) * pow14_68_mul_t z := by
  simp only [pow14_34, pow14_68_q, f, pow14_68, pow14_68_mul_t]
  
  ring

theorem pow14_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_34 z * pow14_34 z = pow14_68_q z * f z + pow14_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_68_mul_integer z


theorem pow14_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_34 z * pow14_34 z = pow14_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_68_mul z


theorem pow14_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 68 = pow14_68 z := by
  calc
    _ = u13 z ^ 34 * u13 z ^ 34 := by ring
    _ = pow14_34 z * pow14_34 z := by rw [pow14_34_pow z hz]
    _ = _ := pow14_68_root z hz


def pow14_69 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (24 + z * (37 + z * (52 + z * (27 + z * (39 + z * (119 + z * (23 + z * (10 + z * (50 + z * (76 + z * (29 + z * (130 + z * (86 + z * (17 + z * (58 + z * (52 + z * (87 + z * (88 + z * 64)))))))))))))))))))

def pow14_69_q {R : Type*} [CommRing R] (z : R) : R := (129 + z * (101 + z * (13 + z * (121 + z * (6 + z * (34 + z * (84 + z * (28 + z * (70 + z * (51 + z * (87 + z * (6 + z * (136 + z * (11 + z * (15 + z * (106 + z * (7 + z * (7 + z * 131))))))))))))))))))

def pow14_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-80) + z * ((-120) + z * ((-87) + z * ((-134) + z * ((-88) + z * ((-27) + z * ((-2) + z * ((-41) + z * (36 + z * ((-7) + z * ((-128) + z * (24 + z * ((-95) + z * ((-144) + z * ((-85) + z * ((-96) + z * ((-99) + z * (42 + z * ((-186) + z * ((-320) + z * ((-77) + z * ((-113) + z * ((-277) + z * (56 + z * ((-73) + z * ((-137) + z * ((-107) + z * ((-120) + z * ((-212) + z * ((-22) + z * ((-78) + z * ((-262) + z * (94 + z * ((-64) + z * ((-105) + z * (4 + z * ((-61) + z * ((-105) + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow14_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_68 z * u13 z = pow14_69_q z * f z + pow14_69 z + (139 : R) * pow14_69_mul_t z := by
  simp only [pow14_68, u13, pow14_69_q, f, pow14_69, pow14_69_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_68 z * u13 z = pow14_69_q z * f z + pow14_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_69_mul_integer z


theorem pow14_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_68 z * u13 z = pow14_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_69_mul z


theorem pow14_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 69 = pow14_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow14_68_pow z hz]
  exact pow14_69_root z hz


def pow14_138 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (56 + z * (10 + z * (89 + z * (92 + z * (56 + z * (25 + z * (87 + z * (37 + z * (9 + z * (10 + z * (28 + z * (52 + z * (58 + z * (55 + z * (84 + z * (89 + z * (88 + z * (47 + z * 97)))))))))))))))))))

def pow14_138_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (87 + z * (88 + z * (35 + z * (59 + z * (99 + z * (102 + z * (70 + z * (60 + z * (68 + z * (129 + z * (129 + z * (82 + z * (70 + z * (26 + z * (123 + z * (15 + z * (25 + z * 65))))))))))))))))))

def pow14_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-117) + z * ((-170) + z * ((-181) + z * ((-246) + z * ((-239) + z * ((-134) + z * ((-309) + z * ((-364) + z * ((-354) + z * ((-428) + z * ((-500) + z * ((-283) + z * ((-468) + z * ((-585) + z * ((-495) + z * ((-442) + z * ((-371) + z * ((-297) + z * ((-407) + z * ((-532) + z * ((-359) + z * ((-190) + z * ((-210) + z * ((-205) + z * ((-202) + z * ((-243) + z * ((-114) + z * ((-120) + z * ((-27) + z * (10 + z * ((-18) + z * (53 + z * ((-23) + z * ((-5) + z * (125 + z * (65 + z * (21 + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow14_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_69 z * pow14_69 z = pow14_138_q z * f z + pow14_138 z + (139 : R) * pow14_138_mul_t z := by
  simp only [pow14_69, pow14_138_q, f, pow14_138, pow14_138_mul_t]
  
  ring

theorem pow14_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_69 z * pow14_69 z = pow14_138_q z * f z + pow14_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_138_mul_integer z


theorem pow14_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_69 z * pow14_69 z = pow14_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_138_mul z


theorem pow14_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 138 = pow14_138 z := by
  calc
    _ = u13 z ^ 69 * u13 z ^ 69 := by ring
    _ = pow14_69 z * pow14_69 z := by rw [pow14_69_pow z hz]
    _ = _ := pow14_138_root z hz


def pow14_139 {R : Type*} [CommRing R] (z : R) : R := (102 + z * (126 + z * (14 + z * (108 + z * (2 + z * (133 + z * (5 + z * (72 + z * (44 + z * (33 + z * (117 + z * (67 + z * (127 + z * (118 + z * (87 + z * (46 + z * (24 + z * (117 + z * (56 + z * 77)))))))))))))))))))

def pow14_139_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (49 + z * (76 + z * (0 + z * (76 + z * (71 + z * (29 + z * (47 + z * (18 + z * (97 + z * (24 + z * (69 + z * (24 + z * (109 + z * (84 + z * (11 + z * (8 + z * (114 + z * 45))))))))))))))))))

def pow14_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * (69 + z * (53 + z * (109 + z * (74 + z * (49 + z * (37 + z * (137 + z * (95 + z * ((-33) + z * (60 + z * ((-30) + z * ((-110) + z * ((-104) + z * ((-122) + z * ((-53) + z * ((-47) + z * ((-70) + z * ((-38) + z * (90 + z * ((-76) + z * ((-79) + z * (55 + z * ((-65) + z * ((-57) + z * ((-65) + z * ((-4) + z * ((-148) + z * ((-97) + z * ((-21) + z * ((-59) + z * ((-20) + z * ((-53) + z * ((-55) + z * (142 + z * (25 + z * ((-2) + z * (8 + z * 89))))))))))))))))))))))))))))))))))))))

theorem pow14_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_138 z * u13 z = pow14_139_q z * f z + pow14_139 z + (139 : R) * pow14_139_mul_t z := by
  simp only [pow14_138, u13, pow14_139_q, f, pow14_139, pow14_139_mul_t]
  simp only [pow13_139]
  ring

theorem pow14_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow14_138 z * u13 z = pow14_139_q z * f z + pow14_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow14_139_mul_integer z


theorem pow14_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow14_138 z * u13 z = pow14_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_139_mul z


theorem pow14_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u13 z ^ 139 = pow14_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow14_138_pow z hz]
  exact pow14_139_root z hz


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_139 z

theorem iterate14 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 14) = u14 z := by
  calc
    _ = (z ^ (139 ^ 13)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate13 z hz)
    _ = _ := pow14_139_pow z hz

end DimensionTen.Mod139

end

end OAI
