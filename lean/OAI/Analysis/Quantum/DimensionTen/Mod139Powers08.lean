import OAI.Analysis.Quantum.DimensionTen.Mod139Powers07

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow15_2 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (44 + z * (117 + z * (109 + z * (125 + z * (57 + z * (49 + z * (116 + z * (37 + z * (132 + z * (115 + z * (36 + z * (125 + z * (48 + z * (90 + z * (58 + z * (121 + z * (14 + z * (23 + z * 38)))))))))))))))))))

def pow15_2_q {R : Type*} [CommRing R] (z : R) : R := (57 + z * (14 + z * (23 + z * (36 + z * (41 + z * (95 + z * (53 + z * (60 + z * (56 + z * (130 + z * (27 + z * (126 + z * (64 + z * (122 + z * (112 + z * (3 + z * (14 + z * (34 + z * 91))))))))))))))))))

def pow15_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (124 + z * (53 + z * (69 + z * (58 + z * (30 + z * (96 + z * ((-144) + z * (79 + z * ((-267) + z * (52 + z * ((-77) + z * ((-12) + z * (47 + z * ((-106) + z * (12 + z * ((-158) + z * (138 + z * (31 + z * ((-13) + z * (112 + z * ((-210) + z * (108 + z * ((-48) + z * (87 + z * (55 + z * (52 + z * ((-37) + z * ((-1) + z * (161 + z * (102 + z * (138 + z * (16 + z * ((-19) + z * (79 + z * (83 + z * (54 + z * ((-22) + z * 42))))))))))))))))))))))))))))))))))))))

theorem pow15_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z + (139 : R) * pow15_2_mul_t z := by
  simp only [u14, pow15_2_q, f, pow15_2, pow15_2_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_2_mul_integer z


theorem pow15_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z * u14 z = pow15_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_2_mul z


theorem pow15_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 2 = pow15_2 z := by
  calc
    _ = u14 z ^ 1 * u14 z ^ 1 := by ring
    _ = u14 z * u14 z := by simp only [pow_one]
    _ = _ := pow15_2_root z hz


def pow15_4 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (131 + z * (134 + z * (32 + z * (83 + z * (1 + z * (92 + z * (5 + z * (73 + z * (37 + z * (45 + z * (21 + z * (82 + z * (57 + z * (42 + z * (90 + z * (79 + z * (110 + z * (105 + z * 96)))))))))))))))))))

def pow15_4_q {R : Type*} [CommRing R] (z : R) : R := (41 + z * (132 + z * (31 + z * (2 + z * (18 + z * (29 + z * (45 + z * (34 + z * (68 + z * (96 + z * (72 + z * (27 + z * (36 + z * (3 + z * (83 + z * (14 + z * (24 + z * (118 + z * 54))))))))))))))))))

def pow15_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (56 + z * ((-67) + z * (22 + z * (60 + z * (164 + z * (168 + z * (253 + z * (319 + z * (145 + z * (246 + z * (167 + z * (198 + z * (416 + z * (375 + z * (410 + z * (304 + z * (542 + z * (239 + z * (303 + z * (316 + z * (129 + z * (276 + z * (255 + z * (261 + z * (98 + z * (144 + z * (156 + z * ((-112) + z * (127 + z * (47 + z * ((-12) + z * (41 + z * ((-9) + z * ((-127) + z * ((-3) + z * ((-38) + z * ((-137) + z * ((-38) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (139 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

theorem pow15_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_4_mul_integer z


theorem pow15_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_2 z * pow15_2 z = pow15_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_4_mul z


theorem pow15_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 4 = pow15_4 z := by
  calc
    _ = u14 z ^ 2 * u14 z ^ 2 := by ring
    _ = pow15_2 z * pow15_2 z := by rw [pow15_2_pow z hz]
    _ = _ := pow15_4_root z hz


def pow15_8 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (74 + z * (84 + z * (57 + z * (28 + z * (121 + z * (72 + z * (108 + z * (64 + z * (78 + z * (98 + z * (2 + z * (49 + z * (14 + z * (75 + z * (46 + z * (17 + z * (52 + z * (126 + z * 91)))))))))))))))))))

def pow15_8_q {R : Type*} [CommRing R] (z : R) : R := (117 + z * (2 + z * (110 + z * (5 + z * (88 + z * (105 + z * (49 + z * (29 + z * (125 + z * (25 + z * (41 + z * (22 + z * (94 + z * (36 + z * (138 + z * (135 + z * (55 + z * (50 + z * 42))))))))))))))))))

def pow15_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-88) + z * ((-84) + z * ((-46) + z * (44 + z * ((-61) + z * ((-85) + z * ((-157) + z * ((-132) + z * ((-191) + z * ((-278) + z * ((-145) + z * ((-241) + z * ((-219) + z * ((-260) + z * ((-190) + z * ((-492) + z * ((-276) + z * ((-270) + z * ((-283) + z * ((-16) + z * (45 + z * ((-104) + z * ((-149) + z * ((-181) + z * ((-274) + z * ((-51) + z * ((-97) + z * ((-94) + z * ((-73) + z * (41 + z * ((-22) + z * (47 + z * (99 + z * (24 + z * (130 + z * (187 + z * (154 + z * (106 + z * 66))))))))))))))))))))))))))))))))))))))

theorem pow15_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z + (139 : R) * pow15_8_mul_t z := by
  simp only [pow15_4, pow15_8_q, f, pow15_8, pow15_8_mul_t]
  
  ring

theorem pow15_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_4 z * pow15_4 z = pow15_8_q z * f z + pow15_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_8_mul_integer z


theorem pow15_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_4 z * pow15_4 z = pow15_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_8_mul z


theorem pow15_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 8 = pow15_8 z := by
  calc
    _ = u14 z ^ 4 * u14 z ^ 4 := by ring
    _ = pow15_4 z * pow15_4 z := by rw [pow15_4_pow z hz]
    _ = _ := pow15_8_root z hz


def pow15_16 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (74 + z * (103 + z * (96 + z * (73 + z * (109 + z * (124 + z * (31 + z * (78 + z * (14 + z * (20 + z * (58 + z * (3 + z * (54 + z * (112 + z * (68 + z * (17 + z * (17 + z * (7 + z * 54)))))))))))))))))))

def pow15_16_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (80 + z * (79 + z * (95 + z * (53 + z * (84 + z * (38 + z * (60 + z * (130 + z * (97 + z * (22 + z * (54 + z * (134 + z * (132 + z * (70 + z * (136 + z * (0 + z * (43 + z * 80))))))))))))))))))

def pow15_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-50) + z * ((-72) + z * ((-135) + z * ((-187) + z * ((-138) + z * ((-95) + z * ((-18) + z * ((-77) + z * ((-158) + z * ((-104) + z * ((-181) + z * ((-180) + z * ((-329) + z * ((-281) + z * ((-367) + z * ((-472) + z * ((-353) + z * ((-443) + z * ((-200) + z * ((-155) + z * ((-351) + z * ((-335) + z * ((-169) + z * ((-74) + z * ((-138) + z * ((-117) + z * ((-240) + z * ((-204) + z * ((-79) + z * ((-218) + z * ((-270) + z * ((-44) + z * ((-58) + z * ((-82) + z * (84 + z * (84 + z * (91 + z * 59))))))))))))))))))))))))))))))))))))))

theorem pow15_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z + (139 : R) * pow15_16_mul_t z := by
  simp only [pow15_8, pow15_16_q, f, pow15_16, pow15_16_mul_t]
  
  ring

theorem pow15_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_8 z * pow15_8 z = pow15_16_q z * f z + pow15_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_16_mul_integer z


theorem pow15_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_8 z * pow15_8 z = pow15_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_16_mul z


theorem pow15_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 16 = pow15_16 z := by
  calc
    _ = u14 z ^ 8 * u14 z ^ 8 := by ring
    _ = pow15_8 z * pow15_8 z := by rw [pow15_8_pow z hz]
    _ = _ := pow15_16_root z hz


def pow15_17 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (85 + z * (103 + z * (63 + z * (39 + z * (82 + z * (63 + z * (119 + z * (81 + z * (88 + z * (17 + z * (8 + z * (30 + z * (81 + z * (73 + z * (54 + z * (58 + z * (60 + z * (33 + z * 17)))))))))))))))))))

def pow15_17_q {R : Type*} [CommRing R] (z : R) : R := (133 + z * (29 + z * (56 + z * (44 + z * (73 + z * (93 + z * (66 + z * (104 + z * (129 + z * (96 + z * (27 + z * (117 + z * (11 + z * (114 + z * (92 + z * (129 + z * (2 + z * (95 + z * 127))))))))))))))))))

def pow15_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-61) + z * ((-36) + z * ((-40) + z * ((-22) + z * ((-67) + z * ((-2) + z * (8 + z * ((-92) + z * ((-183) + z * ((-269) + z * ((-322) + z * ((-199) + z * ((-229) + z * ((-216) + z * ((-165) + z * ((-253) + z * ((-245) + z * ((-315) + z * ((-398) + z * ((-304) + z * ((-254) + z * ((-397) + z * ((-295) + z * ((-326) + z * ((-329) + z * ((-224) + z * ((-291) + z * ((-353) + z * ((-243) + z * ((-168) + z * ((-218) + z * ((-161) + z * ((-97) + z * ((-198) + z * ((-149) + z * ((-41) + z * ((-123) + z * ((-92) + z * 29))))))))))))))))))))))))))))))))))))))

theorem pow15_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_16 z * u14 z = pow15_17_q z * f z + pow15_17 z + (139 : R) * pow15_17_mul_t z := by
  simp only [pow15_16, u14, pow15_17_q, f, pow15_17, pow15_17_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_16 z * u14 z = pow15_17_q z * f z + pow15_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_17_mul_integer z


theorem pow15_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_16 z * u14 z = pow15_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_17_mul z


theorem pow15_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 17 = pow15_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow15_16_pow z hz]
  exact pow15_17_root z hz


def pow15_34 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (118 + z * (98 + z * (84 + z * (14 + z * (119 + z * (63 + z * (89 + z * (54 + z * (11 + z * (65 + z * (15 + z * (93 + z * (54 + z * (65 + z * (70 + z * (118 + z * (106 + z * (20 + z * 75)))))))))))))))))))

def pow15_34_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (46 + z * (87 + z * (128 + z * (65 + z * (124 + z * (59 + z * (130 + z * (0 + z * (133 + z * (126 + z * (28 + z * (71 + z * (11 + z * (110 + z * (57 + z * (112 + z * (131 + z * 11))))))))))))))))))

def pow15_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-28) + z * ((-42) + z * ((-90) + z * ((-135) + z * ((-225) + z * ((-217) + z * ((-207) + z * ((-93) + z * ((-121) + z * ((-198) + z * ((-278) + z * ((-355) + z * ((-357) + z * ((-237) + z * ((-232) + z * ((-337) + z * ((-461) + z * ((-478) + z * ((-491) + z * ((-414) + z * ((-287) + z * ((-274) + z * ((-323) + z * ((-315) + z * ((-407) + z * ((-308) + z * ((-260) + z * ((-285) + z * ((-222) + z * ((-211) + z * ((-104) + z * ((-148) + z * ((-166) + z * ((-78) + z * ((-157) + z * ((-107) + z * ((-3) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow15_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_17 z * pow15_17 z = pow15_34_q z * f z + pow15_34 z + (139 : R) * pow15_34_mul_t z := by
  simp only [pow15_17, pow15_34_q, f, pow15_34, pow15_34_mul_t]
  
  ring

theorem pow15_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_17 z * pow15_17 z = pow15_34_q z * f z + pow15_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_34_mul_integer z


theorem pow15_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_17 z * pow15_17 z = pow15_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_34_mul z


theorem pow15_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 34 = pow15_34 z := by
  calc
    _ = u14 z ^ 17 * u14 z ^ 17 := by ring
    _ = pow15_17 z * pow15_17 z := by rw [pow15_17_pow z hz]
    _ = _ := pow15_34_root z hz


def pow15_68 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (131 + z * (113 + z * (29 + z * (52 + z * (23 + z * (57 + z * (1 + z * (101 + z * (113 + z * (33 + z * (64 + z * (12 + z * (61 + z * (61 + z * (16 + z * (123 + z * (82 + z * (38 + z * 50)))))))))))))))))))

def pow15_68_q {R : Type*} [CommRing R] (z : R) : R := (111 + z * (23 + z * (104 + z * (17 + z * (126 + z * (56 + z * (88 + z * (29 + z * (53 + z * (29 + z * (99 + z * (50 + z * (138 + z * (108 + z * (103 + z * (125 + z * (78 + z * (101 + z * 65))))))))))))))))))

def pow15_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (88 + z * (70 + z * (81 + z * ((-77) + z * (29 + z * (9 + z * (62 + z * (65 + z * ((-96) + z * ((-72) + z * ((-143) + z * ((-113) + z * ((-202) + z * ((-292) + z * ((-265) + z * ((-271) + z * ((-52) + z * ((-234) + z * ((-174) + z * ((-228) + z * ((-224) + z * ((-128) + z * ((-293) + z * ((-136) + z * ((-325) + z * ((-230) + z * ((-214) + z * ((-253) + z * ((-75) + z * ((-186) + z * ((-130) + z * ((-49) + z * ((-43) + z * ((-37) + z * (11 + z * ((-24) + z * ((-39) + z * 40))))))))))))))))))))))))))))))))))))))

theorem pow15_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_34 z * pow15_34 z = pow15_68_q z * f z + pow15_68 z + (139 : R) * pow15_68_mul_t z := by
  simp only [pow15_34, pow15_68_q, f, pow15_68, pow15_68_mul_t]
  
  ring

theorem pow15_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_34 z * pow15_34 z = pow15_68_q z * f z + pow15_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_68_mul_integer z


theorem pow15_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_34 z * pow15_34 z = pow15_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_68_mul z


theorem pow15_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 68 = pow15_68 z := by
  calc
    _ = u14 z ^ 34 * u14 z ^ 34 := by ring
    _ = pow15_34 z * pow15_34 z := by rw [pow15_34_pow z hz]
    _ = _ := pow15_68_root z hz


def pow15_69 {R : Type*} [CommRing R] (z : R) : R := (65 + z * (108 + z * (42 + z * (136 + z * (40 + z * (116 + z * (97 + z * (71 + z * (3 + z * (24 + z * (121 + z * (121 + z * (136 + z * (134 + z * (29 + z * (103 + z * (12 + z * (35 + z * (77 + z * 66)))))))))))))))))))

def pow15_69_q {R : Type*} [CommRing R] (z : R) : R := (111 + z * (130 + z * (78 + z * (131 + z * (130 + z * (62 + z * (131 + z * (115 + z * (59 + z * (108 + z * (85 + z * (121 + z * (112 + z * (32 + z * (97 + z * (52 + z * (30 + z * (121 + z * 97))))))))))))))))))

def pow15_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-6) + z * ((-61) + z * ((-173) + z * ((-315) + z * ((-233) + z * ((-313) + z * ((-352) + z * ((-393) + z * ((-311) + z * ((-493) + z * ((-390) + z * ((-398) + z * ((-433) + z * ((-346) + z * ((-479) + z * ((-461) + z * ((-436) + z * ((-418) + z * ((-487) + z * ((-516) + z * ((-345) + z * ((-455) + z * ((-253) + z * ((-320) + z * ((-360) + z * ((-151) + z * ((-230) + z * ((-95) + z * ((-23) + z * ((-145) + z * ((-76) + z * ((-58) + z * ((-89) + z * ((-1) + z * (25 + z * ((-80) + z * ((-49) + z * 27))))))))))))))))))))))))))))))))))))))

theorem pow15_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_68 z * u14 z = pow15_69_q z * f z + pow15_69 z + (139 : R) * pow15_69_mul_t z := by
  simp only [pow15_68, u14, pow15_69_q, f, pow15_69, pow15_69_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_68 z * u14 z = pow15_69_q z * f z + pow15_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_69_mul_integer z


theorem pow15_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_68 z * u14 z = pow15_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_69_mul z


theorem pow15_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 69 = pow15_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow15_68_pow z hz]
  exact pow15_69_root z hz


def pow15_138 {R : Type*} [CommRing R] (z : R) : R := (127 + z * (18 + z * (8 + z * (95 + z * (102 + z * (102 + z * (77 + z * (96 + z * (8 + z * (112 + z * (80 + z * (74 + z * (60 + z * (129 + z * (16 + z * (12 + z * (17 + z * (29 + z * (0 + z * 35)))))))))))))))))))

def pow15_138_q {R : Type*} [CommRing R] (z : R) : R := (43 + z * (118 + z * (74 + z * (70 + z * (82 + z * (117 + z * (134 + z * (56 + z * (127 + z * (90 + z * (91 + z * (43 + z * (135 + z * (51 + z * (105 + z * (83 + z * (92 + z * (117 + z * 47))))))))))))))))))

def pow15_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-26) + z * ((-75) + z * ((-73) + z * ((-75) + z * ((-147) + z * ((-25) + z * ((-120) + z * ((-167) + z * ((-316) + z * ((-264) + z * ((-188) + z * ((-127) + z * ((-11) + z * ((-173) + z * ((-137) + z * ((-65) + z * ((-246) + z * ((-149) + z * ((-360) + z * ((-256) + z * ((-258) + z * ((-83) + z * ((-33) + z * ((-93) + z * ((-62) + z * ((-145) + z * ((-252) + z * ((-66) + z * ((-2) + z * ((-25) + z * ((-73) + z * ((-84) + z * ((-138) + z * ((-64) + z * ((-121) + z * ((-67) + z * (29 + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow15_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_69 z * pow15_69 z = pow15_138_q z * f z + pow15_138 z + (139 : R) * pow15_138_mul_t z := by
  simp only [pow15_69, pow15_138_q, f, pow15_138, pow15_138_mul_t]
  
  ring

theorem pow15_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_69 z * pow15_69 z = pow15_138_q z * f z + pow15_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_138_mul_integer z


theorem pow15_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_69 z * pow15_69 z = pow15_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_138_mul z


theorem pow15_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 138 = pow15_138 z := by
  calc
    _ = u14 z ^ 69 * u14 z ^ 69 := by ring
    _ = pow15_69 z * pow15_69 z := by rw [pow15_69_pow z hz]
    _ = _ := pow15_138_root z hz


def pow15_139 {R : Type*} [CommRing R] (z : R) : R := (134 + z * (115 + z * (50 + z * (21 + z * (78 + z * (128 + z * (94 + z * (113 + z * (17 + z * (72 + z * (82 + z * (137 + z * (28 + z * (122 + z * (89 + z * (66 + z * (119 + z * (120 + z * (87 + z * 10)))))))))))))))))))

def pow15_139_q {R : Type*} [CommRing R] (z : R) : R := (89 + z * (72 + z * (72 + z * (17 + z * (81 + z * (17 + z * (125 + z * (44 + z * (35 + z * (91 + z * (51 + z * (29 + z * (2 + z * (29 + z * (75 + z * (20 + z * (2 + z * (52 + z * 54))))))))))))))))))

def pow15_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (25 + z * ((-5) + z * ((-163) + z * ((-48) + z * ((-102) + z * (53 + z * ((-53) + z * ((-40) + z * ((-55) + z * ((-157) + z * ((-21) + z * ((-83) + z * (119 + z * (58 + z * (127 + z * ((-24) + z * (41 + z * (123 + z * (67 + z * ((-53) + z * (29 + z * (80 + z * (116 + z * (164 + z * (117 + z * (7 + z * (140 + z * ((-11) + z * (11 + z * (54 + z * (66 + z * (43 + z * ((-9) + z * ((-107) + z * ((-16) + z * ((-13) + z * ((-42) + z * ((-36) + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow15_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_138 z * u14 z = pow15_139_q z * f z + pow15_139 z + (139 : R) * pow15_139_mul_t z := by
  simp only [pow15_138, u14, pow15_139_q, f, pow15_139, pow15_139_mul_t]
  simp only [pow14_139]
  ring

theorem pow15_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow15_138 z * u14 z = pow15_139_q z * f z + pow15_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow15_139_mul_integer z


theorem pow15_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow15_138 z * u14 z = pow15_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_139_mul z


theorem pow15_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u14 z ^ 139 = pow15_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow15_138_pow z hz]
  exact pow15_139_root z hz


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_139 z

theorem iterate15 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 15) = u15 z := by
  calc
    _ = (z ^ (139 ^ 14)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u14 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate14 z hz)
    _ = _ := pow15_139_pow z hz


def pow16_2 {R : Type*} [CommRing R] (z : R) : R := (108 + z * (110 + z * (20 + z * (130 + z * (133 + z * (8 + z * (121 + z * (19 + z * (122 + z * (62 + z * (119 + z * (83 + z * (11 + z * (118 + z * (99 + z * (102 + z * (0 + z * (120 + z * (110 + z * 20)))))))))))))))))))

def pow16_2_q {R : Type*} [CommRing R] (z : R) : R := (121 + z * (136 + z * (134 + z * (133 + z * (119 + z * (27 + z * (43 + z * (69 + z * (12 + z * (138 + z * (4 + z * (19 + z * (8 + z * (69 + z * (90 + z * (36 + z * (12 + z * (60 + z * 100))))))))))))))))))

def pow16_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (37 + z * (12 + z * ((-138) + z * ((-333) + z * ((-349) + z * ((-124) + z * ((-26) + z * (3 + z * ((-88) + z * ((-155) + z * ((-121) + z * (111 + z * (63 + z * (6 + z * (129 + z * (133 + z * (165 + z * (250 + z * (317 + z * ((-3) + z * (168 + z * (223 + z * (238 + z * (349 + z * (394 + z * (215 + z * (270 + z * (249 + z * (204 + z * (328 + z * (242 + z * (209 + z * (125 + z * (77 + z * (136 + z * (112 + z * ((-57) + z * ((-80) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow16_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z + (139 : R) * pow16_2_mul_t z := by
  simp only [u15, pow16_2_q, f, pow16_2, pow16_2_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_2_mul_integer z


theorem pow16_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z * u15 z = pow16_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_2_mul z


theorem pow16_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 2 = pow16_2 z := by
  calc
    _ = u15 z ^ 1 * u15 z ^ 1 := by ring
    _ = u15 z * u15 z := by simp only [pow_one]
    _ = _ := pow16_2_root z hz


def pow16_4 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (89 + z * (68 + z * (8 + z * (60 + z * (66 + z * (107 + z * (61 + z * (90 + z * (76 + z * (63 + z * (10 + z * (103 + z * (67 + z * (27 + z * (74 + z * (35 + z * (104 + z * (82 + z * 52)))))))))))))))))))

def pow16_4_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (118 + z * (120 + z * (39 + z * (109 + z * (123 + z * (46 + z * (125 + z * (126 + z * (70 + z * (89 + z * (18 + z * (102 + z * (23 + z * (0 + z * (61 + z * (64 + z * (43 + z * 122))))))))))))))))))

def pow16_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-11) + z * ((-171) + z * ((-107) + z * ((-4) + z * ((-202) + z * ((-84) + z * ((-43) + z * ((-230) + z * ((-149) + z * ((-179) + z * ((-139) + z * ((-85) + z * ((-111) + z * (186 + z * ((-108) + z * ((-33) + z * (62 + z * (100 + z * ((-6) + z * ((-242) + z * (218 + z * ((-26) + z * (83 + z * (93 + z * (22 + z * (4 + z * (89 + z * (161 + z * (92 + z * (92 + z * (26 + z * (213 + z * (31 + z * ((-72) + z * (99 + z * ((-8) + z * ((-81) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow16_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z + (139 : R) * pow16_4_mul_t z := by
  simp only [pow16_2, pow16_4_q, f, pow16_4, pow16_4_mul_t]
  
  ring

theorem pow16_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_4_mul_integer z


theorem pow16_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_2 z * pow16_2 z = pow16_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_4_mul z


theorem pow16_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 4 = pow16_4 z := by
  calc
    _ = u15 z ^ 2 * u15 z ^ 2 := by ring
    _ = pow16_2 z * pow16_2 z := by rw [pow16_2_pow z hz]
    _ = _ := pow16_4_root z hz


def pow16_8 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (82 + z * (88 + z * (48 + z * (83 + z * (30 + z * (71 + z * (4 + z * (117 + z * (50 + z * (105 + z * (86 + z * (15 + z * (38 + z * (37 + z * (70 + z * (16 + z * (128 + z * (128 + z * 131)))))))))))))))))))

def pow16_8_q {R : Type*} [CommRing R] (z : R) : R := (52 + z * (57 + z * (50 + z * (95 + z * (105 + z * (99 + z * (53 + z * (41 + z * (40 + z * (131 + z * (22 + z * (119 + z * (37 + z * (62 + z * (25 + z * (117 + z * (94 + z * (47 + z * 63))))))))))))))))))

def pow16_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (17 + z * (3 + z * ((-120) + z * ((-188) + z * ((-197) + z * ((-115) + z * ((-123) + z * ((-74) + z * ((-133) + z * ((-104) + z * ((-238) + z * ((-184) + z * ((-204) + z * ((-127) + z * ((-220) + z * ((-256) + z * ((-193) + z * ((-214) + z * ((-251) + z * ((-205) + z * ((-157) + z * ((-174) + z * ((-63) + z * ((-113) + z * ((-69) + z * ((-55) + z * ((-63) + z * ((-148) + z * ((-63) + z * ((-49) + z * ((-83) + z * ((-9) + z * ((-29) + z * ((-55) + z * (27 + z * (36 + z * (3 + z * 19))))))))))))))))))))))))))))))))))))))

theorem pow16_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z + (139 : R) * pow16_8_mul_t z := by
  simp only [pow16_4, pow16_8_q, f, pow16_8, pow16_8_mul_t]
  
  ring

theorem pow16_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_4 z * pow16_4 z = pow16_8_q z * f z + pow16_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_8_mul_integer z


theorem pow16_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_4 z * pow16_4 z = pow16_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_8_mul z


theorem pow16_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 8 = pow16_8 z := by
  calc
    _ = u15 z ^ 4 * u15 z ^ 4 := by ring
    _ = pow16_4 z * pow16_4 z := by rw [pow16_4_pow z hz]
    _ = _ := pow16_8_root z hz


def pow16_16 {R : Type*} [CommRing R] (z : R) : R := (12 + z * (110 + z * (104 + z * (95 + z * (131 + z * (46 + z * (66 + z * (74 + z * (72 + z * (114 + z * (17 + z * (68 + z * (8 + z * (62 + z * (38 + z * (129 + z * (30 + z * (54 + z * (25 + z * 35)))))))))))))))))))

def pow16_16_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (101 + z * (94 + z * (106 + z * (91 + z * (112 + z * (67 + z * (25 + z * (120 + z * (18 + z * (36 + z * (4 + z * (95 + z * (118 + z * (125 + z * (12 + z * (113 + z * (46 + z * 64))))))))))))))))))

def pow16_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-39) + z * ((-89) + z * ((-122) + z * ((-186) + z * ((-236) + z * ((-273) + z * ((-262) + z * ((-267) + z * ((-278) + z * ((-267) + z * ((-195) + z * ((-196) + z * ((-129) + z * ((-324) + z * ((-357) + z * ((-455) + z * ((-450) + z * ((-425) + z * ((-316) + z * ((-63) + z * ((-128) + z * ((-100) + z * ((-203) + z * ((-91) + z * ((-200) + z * (92 + z * ((-69) + z * (79 + z * (135 + z * (79 + z * (12 + z * ((-153) + z * ((-81) + z * (24 + z * (131 + z * (128 + z * (269 + z * (182 + z * 123))))))))))))))))))))))))))))))))))))))

theorem pow16_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z + (139 : R) * pow16_16_mul_t z := by
  simp only [pow16_8, pow16_16_q, f, pow16_16, pow16_16_mul_t]
  
  ring

theorem pow16_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_8 z * pow16_8 z = pow16_16_q z * f z + pow16_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_16_mul_integer z


theorem pow16_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_8 z * pow16_8 z = pow16_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_16_mul z


theorem pow16_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 16 = pow16_16 z := by
  calc
    _ = u15 z ^ 8 * u15 z ^ 8 := by ring
    _ = pow16_8 z * pow16_8 z := by rw [pow16_8_pow z hz]
    _ = _ := pow16_16_root z hz


def pow16_17 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (32 + z * (25 + z * (28 + z * (120 + z * (29 + z * (50 + z * (26 + z * (20 + z * (87 + z * (93 + z * (12 + z * (121 + z * (100 + z * (112 + z * (102 + z * (104 + z * (109 + z * (67 + z * 120)))))))))))))))))))

def pow16_17_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (93 + z * (23 + z * (99 + z * (98 + z * (14 + z * (117 + z * (137 + z * (30 + z * (31 + z * (55 + z * (26 + z * (22 + z * (40 + z * (95 + z * (29 + z * (48 + z * (56 + z * 72))))))))))))))))))

def pow16_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-91) + z * ((-73) + z * ((-25) + z * ((-88) + z * ((-111) + z * ((-46) + z * ((-45) + z * ((-108) + z * ((-20) + z * ((-19) + z * ((-166) + z * ((-9) + z * (67 + z * ((-22) + z * (17 + z * (144 + z * ((-97) + z * (19 + z * (124 + z * ((-28) + z * (134 + z * (103 + z * (48 + z * ((-37) + z * (137 + z * ((-11) + z * (44 + z * (4 + z * (69 + z * (36 + z * (35 + z * (65 + z * (25 + z * ((-12) + z * ((-10) + z * (2 + z * ((-55) + z * ((-43) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow16_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_16 z * u15 z = pow16_17_q z * f z + pow16_17 z + (139 : R) * pow16_17_mul_t z := by
  simp only [pow16_16, u15, pow16_17_q, f, pow16_17, pow16_17_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_16 z * u15 z = pow16_17_q z * f z + pow16_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_17_mul_integer z


theorem pow16_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_16 z * u15 z = pow16_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_17_mul z


theorem pow16_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 17 = pow16_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow16_16_pow z hz]
  exact pow16_17_root z hz


def pow16_34 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (104 + z * (26 + z * (41 + z * (81 + z * (85 + z * (86 + z * (22 + z * (7 + z * (60 + z * (45 + z * (1 + z * (67 + z * (119 + z * (46 + z * (100 + z * (97 + z * (36 + z * (54 + z * 46)))))))))))))))))))

def pow16_34_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (6 + z * (118 + z * (28 + z * (90 + z * (58 + z * (135 + z * (4 + z * (78 + z * (135 + z * (55 + z * (30 + z * (138 + z * (108 + z * (3 + z * (128 + z * (50 + z * (35 + z * 83))))))))))))))))))

def pow16_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * (0 + z * ((-91) + z * ((-121) + z * ((-75) + z * ((-177) + z * ((-247) + z * ((-227) + z * ((-214) + z * ((-294) + z * ((-252) + z * ((-349) + z * ((-370) + z * ((-295) + z * ((-190) + z * ((-410) + z * ((-225) + z * ((-173) + z * ((-236) + z * ((-138) + z * ((-142) + z * ((-146) + z * ((-137) + z * (107 + z * ((-33) + z * ((-75) + z * (184 + z * (141 + z * (105 + z * (383 + z * (249 + z * (196 + z * (317 + z * (275 + z * (138 + z * (212 + z * (127 + z * (39 + z * 103))))))))))))))))))))))))))))))))))))))

theorem pow16_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_17 z * pow16_17 z = pow16_34_q z * f z + pow16_34 z + (139 : R) * pow16_34_mul_t z := by
  simp only [pow16_17, pow16_34_q, f, pow16_34, pow16_34_mul_t]
  
  ring

theorem pow16_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_17 z * pow16_17 z = pow16_34_q z * f z + pow16_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_34_mul_integer z


theorem pow16_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_17 z * pow16_17 z = pow16_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_34_mul z


theorem pow16_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 34 = pow16_34 z := by
  calc
    _ = u15 z ^ 17 * u15 z ^ 17 := by ring
    _ = pow16_17 z * pow16_17 z := by rw [pow16_17_pow z hz]
    _ = _ := pow16_34_root z hz


def pow16_68 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (8 + z * (110 + z * (107 + z * (80 + z * (3 + z * (78 + z * (91 + z * (63 + z * (33 + z * (65 + z * (101 + z * (61 + z * (94 + z * (69 + z * (8 + z * (37 + z * (51 + z * (28 + z * 59)))))))))))))))))))

def pow16_68_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (112 + z * (122 + z * (107 + z * (137 + z * (80 + z * (117 + z * (18 + z * (13 + z * (68 + z * (49 + z * (10 + z * (110 + z * (80 + z * (91 + z * (69 + z * (27 + z * (27 + z * 31))))))))))))))))))

def pow16_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-46) + z * ((-78) + z * ((-175) + z * ((-304) + z * ((-352) + z * ((-300) + z * ((-303) + z * ((-303) + z * ((-335) + z * ((-322) + z * ((-308) + z * ((-347) + z * ((-438) + z * ((-416) + z * ((-406) + z * ((-457) + z * ((-398) + z * ((-294) + z * ((-270) + z * ((-286) + z * ((-270) + z * ((-244) + z * ((-263) + z * ((-216) + z * ((-184) + z * ((-138) + z * ((-38) + z * ((-84) + z * ((-32) + z * (52 + z * ((-4) + z * (25 + z * (40 + z * ((-19) + z * (41 + z * (47 + z * ((-3) + z * (7 + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow16_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_34 z * pow16_34 z = pow16_68_q z * f z + pow16_68 z + (139 : R) * pow16_68_mul_t z := by
  simp only [pow16_34, pow16_68_q, f, pow16_68, pow16_68_mul_t]
  
  ring

theorem pow16_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_34 z * pow16_34 z = pow16_68_q z * f z + pow16_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_68_mul_integer z


theorem pow16_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_34 z * pow16_34 z = pow16_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_68_mul z


theorem pow16_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 68 = pow16_68 z := by
  calc
    _ = u15 z ^ 34 * u15 z ^ 34 := by ring
    _ = pow16_34 z * pow16_34 z := by rw [pow16_34_pow z hz]
    _ = _ := pow16_68_root z hz


def pow16_69 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (65 + z * (56 + z * (34 + z * (42 + z * (7 + z * (8 + z * (48 + z * (53 + z * (15 + z * (6 + z * (80 + z * (73 + z * (108 + z * (40 + z * (77 + z * (104 + z * (118 + z * (45 + z * 51)))))))))))))))))))

def pow16_69_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (1 + z * (43 + z * (53 + z * (125 + z * (15 + z * (14 + z * (82 + z * (125 + z * (37 + z * (71 + z * (101 + z * (101 + z * (43 + z * (98 + z * (38 + z * (20 + z * (88 + z * 34))))))))))))))))))

def pow16_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (72 + z * (58 + z * (78 + z * (92 + z * (52 + z * (6 + z * (30 + z * (135 + z * (54 + z * (68 + z * ((-37) + z * (34 + z * ((-64) + z * (98 + z * ((-11) + z * ((-10) + z * (35 + z * (51 + z * (52 + z * (93 + z * (43 + z * ((-40) + z * ((-55) + z * ((-46) + z * (85 + z * (33 + z * ((-99) + z * ((-123) + z * (50 + z * (42 + z * ((-51) + z * ((-22) + z * ((-17) + z * ((-77) + z * (41 + z * (26 + z * ((-34) + z * (7 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow16_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_68 z * u15 z = pow16_69_q z * f z + pow16_69 z + (139 : R) * pow16_69_mul_t z := by
  simp only [pow16_68, u15, pow16_69_q, f, pow16_69, pow16_69_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_68 z * u15 z = pow16_69_q z * f z + pow16_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_69_mul_integer z


theorem pow16_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_68 z * u15 z = pow16_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_69_mul z


theorem pow16_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 69 = pow16_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow16_68_pow z hz]
  exact pow16_69_root z hz


def pow16_138 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (49 + z * (119 + z * (63 + z * (52 + z * (14 + z * (28 + z * (121 + z * (33 + z * (114 + z * (19 + z * (31 + z * (78 + z * (80 + z * (106 + z * (130 + z * (128 + z * (25 + z * (52 + z * 45)))))))))))))))))))

def pow16_138_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (11 + z * (104 + z * (128 + z * (128 + z * (15 + z * (109 + z * (116 + z * (113 + z * (17 + z * (113 + z * (136 + z * (96 + z * (89 + z * (53 + z * (84 + z * (129 + z * (119 + z * 99))))))))))))))))))

def pow16_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-38) + z * ((-46) + z * ((-98) + z * ((-190) + z * ((-294) + z * ((-294) + z * ((-385) + z * ((-444) + z * ((-436) + z * ((-424) + z * ((-548) + z * ((-626) + z * ((-646) + z * ((-679) + z * ((-585) + z * ((-603) + z * ((-734) + z * ((-746) + z * ((-725) + z * ((-708) + z * ((-701) + z * ((-719) + z * ((-668) + z * ((-507) + z * ((-360) + z * ((-451) + z * ((-492) + z * ((-308) + z * ((-101) + z * ((-133) + z * ((-92) + z * ((-143) + z * ((-33) + z * ((-18) + z * ((-31) + z * ((-54) + z * ((-82) + z * ((-59) + z * 18))))))))))))))))))))))))))))))))))))))

theorem pow16_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_69 z * pow16_69 z = pow16_138_q z * f z + pow16_138 z + (139 : R) * pow16_138_mul_t z := by
  simp only [pow16_69, pow16_138_q, f, pow16_138, pow16_138_mul_t]
  
  ring

theorem pow16_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_69 z * pow16_69 z = pow16_138_q z * f z + pow16_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_138_mul_integer z


theorem pow16_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_69 z * pow16_69 z = pow16_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_138_mul z


theorem pow16_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 138 = pow16_138 z := by
  calc
    _ = u15 z ^ 69 * u15 z ^ 69 := by ring
    _ = pow16_69 z * pow16_69 z := by rw [pow16_69_pow z hz]
    _ = _ := pow16_138_root z hz


def pow16_139 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (86 + z * (86 + z * (57 + z * (99 + z * (120 + z * (3 + z * (103 + z * (47 + z * (22 + z * (98 + z * (68 + z * (40 + z * (37 + z * (113 + z * (58 + z * (118 + z * (42 + z * (12 + z * 122)))))))))))))))))))

def pow16_139_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (50 + z * (69 + z * (89 + z * (22 + z * (67 + z * (116 + z * (1 + z * (69 + z * (57 + z * (98 + z * (113 + z * (126 + z * (63 + z * (10 + z * (122 + z * (94 + z * (72 + z * 33))))))))))))))))))

def pow16_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (46 + z * (39 + z * (50 + z * ((-24) + z * ((-40) + z * ((-69) + z * ((-101) + z * (81 + z * (21 + z * (21 + z * ((-133) + z * ((-112) + z * ((-187) + z * ((-75) + z * (12 + z * ((-90) + z * ((-8) + z * (18 + z * ((-15) + z * ((-101) + z * (104 + z * ((-113) + z * ((-20) + z * (129 + z * ((-69) + z * ((-19) + z * (40 + z * (32 + z * ((-22) + z * (89 + z * (33 + z * (4 + z * (174 + z * (94 + z * ((-32) + z * ((-32) + z * ((-18) + z * (1 + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow16_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_138 z * u15 z = pow16_139_q z * f z + pow16_139 z + (139 : R) * pow16_139_mul_t z := by
  simp only [pow16_138, u15, pow16_139_q, f, pow16_139, pow16_139_mul_t]
  simp only [pow15_139]
  ring

theorem pow16_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow16_138 z * u15 z = pow16_139_q z * f z + pow16_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow16_139_mul_integer z


theorem pow16_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow16_138 z * u15 z = pow16_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_139_mul z


theorem pow16_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u15 z ^ 139 = pow16_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow16_138_pow z hz]
  exact pow16_139_root z hz


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_139 z

theorem iterate16 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 16) = u16 z := by
  calc
    _ = (z ^ (139 ^ 15)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u15 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate15 z hz)
    _ = _ := pow16_139_pow z hz

end DimensionTen.Mod139

end

end OAI
