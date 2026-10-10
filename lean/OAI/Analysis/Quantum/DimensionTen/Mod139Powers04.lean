import OAI.Analysis.Quantum.DimensionTen.Mod139Powers03

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (98 + z * (47 + z * (78 + z * (15 + z * (135 + z * (52 + z * (87 + z * (82 + z * (19 + z * (8 + z * (41 + z * (82 + z * (109 + z * (41 + z * (89 + z * (65 + z * (123 + z * (87 + z * 45)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (60 + z * (95 + z * (79 + z * (103 + z * (57 + z * (132 + z * (134 + z * (35 + z * (135 + z * (119 + z * (81 + z * (37 + z * (99 + z * (111 + z * (31 + z * (77 + z * (50 + z * (5 + z * 89))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-34) + z * ((-67) + z * ((-109) + z * ((-246) + z * ((-317) + z * ((-319) + z * ((-227) + z * ((-233) + z * ((-318) + z * ((-498) + z * ((-357) + z * ((-424) + z * ((-340) + z * ((-540) + z * ((-307) + z * ((-564) + z * ((-416) + z * ((-453) + z * ((-426) + z * ((-597) + z * ((-389) + z * ((-435) + z * ((-336) + z * ((-138) + z * ((-268) + z * ((-187) + z * ((-228) + z * ((-227) + z * ((-321) + z * ((-147) + z * ((-70) + z * ((-193) + z * ((-29) + z * (10 + z * ((-35) + z * (51 + z * ((-13) + z * ((-55) + z * 5))))))))))))))))))))))))))))))))))))))

theorem pow7_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z + (139 : R) * pow7_2_mul_t z := by
  simp only [u6, pow7_2_q, f, pow7_2, pow7_2_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_2_mul_integer z


theorem pow7_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z * u6 z = pow7_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_2_mul z


theorem pow7_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 2 = pow7_2 z := by
  calc
    _ = u6 z ^ 1 * u6 z ^ 1 := by ring
    _ = u6 z * u6 z := by simp only [pow_one]
    _ = _ := pow7_2_root z hz


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (67 + z * (3 + z * (11 + z * (5 + z * (0 + z * (86 + z * (81 + z * (99 + z * (136 + z * (105 + z * (107 + z * (127 + z * (86 + z * (38 + z * (54 + z * (13 + z * (107 + z * (131 + z * 77)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (87 + z * (28 + z * (137 + z * (138 + z * (83 + z * (70 + z * (73 + z * (111 + z * (109 + z * (22 + z * (74 + z * (19 + z * (67 + z * (115 + z * (66 + z * (74 + z * (81 + z * 79))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-55) + z * ((-98) + z * ((-81) + z * ((-185) + z * ((-262) + z * ((-301) + z * ((-192) + z * ((-298) + z * ((-200) + z * ((-329) + z * ((-327) + z * ((-415) + z * ((-322) + z * ((-316) + z * ((-334) + z * ((-354) + z * ((-417) + z * ((-442) + z * ((-275) + z * ((-352) + z * ((-94) + z * ((-226) + z * ((-224) + z * ((-174) + z * ((-147) + z * ((-63) + z * ((-128) + z * ((-273) + z * ((-76) + z * (17 + z * (71 + z * (68 + z * (17 + z * ((-20) + z * (66 + z * (68 + z * (1 + z * ((-17) + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow7_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z + (139 : R) * pow7_4_mul_t z := by
  simp only [pow7_2, pow7_4_q, f, pow7_4, pow7_4_mul_t]
  
  ring

theorem pow7_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_4_mul_integer z


theorem pow7_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_2 z * pow7_2 z = pow7_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_4_mul z


theorem pow7_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 4 = pow7_4 z := by
  calc
    _ = u6 z ^ 2 * u6 z ^ 2 := by ring
    _ = pow7_2 z * pow7_2 z := by rw [pow7_2_pow z hz]
    _ = _ := pow7_4_root z hz


def pow7_8 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (41 + z * (114 + z * (46 + z * (104 + z * (68 + z * (75 + z * (42 + z * (25 + z * (104 + z * (36 + z * (97 + z * (10 + z * (135 + z * (17 + z * (18 + z * (86 + z * (93 + z * (55 + z * 65)))))))))))))))))))

def pow7_8_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (126 + z * (134 + z * (40 + z * (114 + z * (124 + z * (65 + z * (116 + z * (136 + z * (45 + z * (104 + z * (99 + z * (12 + z * (6 + z * (51 + z * (6 + z * (132 + z * (47 + z * 91))))))))))))))))))

def pow7_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (35 + z * ((-71) + z * ((-279) + z * ((-348) + z * ((-433) + z * ((-486) + z * ((-319) + z * ((-308) + z * ((-395) + z * ((-341) + z * ((-445) + z * ((-509) + z * ((-322) + z * ((-316) + z * ((-463) + z * ((-342) + z * ((-363) + z * ((-243) + z * ((-67) + z * ((-48) + z * ((-300) + z * ((-137) + z * (21 + z * ((-63) + z * (85 + z * (212 + z * (109 + z * (239 + z * (323 + z * (195 + z * (250 + z * (161 + z * (30 + z * (15 + z * ((-12) + z * (60 + z * (131 + z * (61 + z * 42))))))))))))))))))))))))))))))))))))))

theorem pow7_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z + (139 : R) * pow7_8_mul_t z := by
  simp only [pow7_4, pow7_8_q, f, pow7_8, pow7_8_mul_t]
  
  ring

theorem pow7_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_4 z * pow7_4 z = pow7_8_q z * f z + pow7_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_8_mul_integer z


theorem pow7_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_4 z * pow7_4 z = pow7_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_8_mul z


theorem pow7_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 8 = pow7_8 z := by
  calc
    _ = u6 z ^ 4 * u6 z ^ 4 := by ring
    _ = pow7_4 z * pow7_4 z := by rw [pow7_4_pow z hz]
    _ = _ := pow7_8_root z hz


def pow7_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (3 + z * (106 + z * (95 + z * (136 + z * (6 + z * (95 + z * (130 + z * (13 + z * (63 + z * (21 + z * (89 + z * (120 + z * (66 + z * (8 + z * (107 + z * (95 + z * (73 + z * (35 + z * 55)))))))))))))))))))

def pow7_16_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (94 + z * (88 + z * (95 + z * (34 + z * (108 + z * (21 + z * (109 + z * (2 + z * (0 + z * (126 + z * (62 + z * (33 + z * (89 + z * (36 + z * (36 + z * (12 + z * (110 + z * 55))))))))))))))))))

def pow7_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-93) + z * ((-40) + z * ((-188) + z * ((-65) + z * ((-135) + z * ((-14) + z * ((-127) + z * ((-102) + z * ((-29) + z * ((-209) + z * ((-45) + z * ((-207) + z * ((-4) + z * ((-281) + z * ((-86) + z * ((-178) + z * ((-55) + z * ((-94) + z * ((-112) + z * ((-197) + z * ((-134) + z * (126 + z * ((-124) + z * (27 + z * ((-87) + z * ((-96) + z * ((-3) + z * ((-2) + z * ((-29) + z * (46 + z * ((-70) + z * (5 + z * ((-42) + z * (59 + z * (62 + z * ((-33) + z * (0 + z * 30))))))))))))))))))))))))))))))))))))))

theorem pow7_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z + (139 : R) * pow7_16_mul_t z := by
  simp only [pow7_8, pow7_16_q, f, pow7_16, pow7_16_mul_t]
  
  ring

theorem pow7_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_8 z * pow7_8 z = pow7_16_q z * f z + pow7_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_16_mul_integer z


theorem pow7_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_8 z * pow7_8 z = pow7_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_16_mul z


theorem pow7_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 16 = pow7_16 z := by
  calc
    _ = u6 z ^ 8 * u6 z ^ 8 := by ring
    _ = pow7_8 z * pow7_8 z := by rw [pow7_8_pow z hz]
    _ = _ := pow7_16_root z hz


def pow7_17 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (92 + z * (3 + z * (136 + z * (57 + z * (82 + z * (71 + z * (34 + z * (85 + z * (46 + z * (36 + z * (102 + z * (33 + z * (132 + z * (96 + z * (69 + z * (8 + z * (75 + z * (1 + z * 5)))))))))))))))))))

def pow7_17_q {R : Type*} [CommRing R] (z : R) : R := (86 + z * (87 + z * (86 + z * (10 + z * (120 + z * (106 + z * (51 + z * (126 + z * (40 + z * (130 + z * (114 + z * (62 + z * (55 + z * (39 + z * (87 + z * (40 + z * (109 + z * (60 + z * 11))))))))))))))))))

def pow7_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-65) + z * ((-141) + z * ((-186) + z * ((-139) + z * ((-199) + z * ((-244) + z * ((-300) + z * ((-233) + z * ((-225) + z * ((-237) + z * ((-418) + z * ((-308) + z * ((-250) + z * ((-228) + z * ((-447) + z * ((-423) + z * ((-314) + z * ((-418) + z * ((-278) + z * ((-400) + z * ((-282) + z * ((-94) + z * ((-46) + z * ((-273) + z * ((-126) + z * ((-204) + z * ((-194) + z * ((-148) + z * ((-90) + z * ((-132) + z * ((-74) + z * ((-4) + z * ((-45) + z * (12 + z * (19 + z * ((-34) + z * ((-8) + z * (23 + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow7_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_16 z * u6 z = pow7_17_q z * f z + pow7_17 z + (139 : R) * pow7_17_mul_t z := by
  simp only [pow7_16, u6, pow7_17_q, f, pow7_17, pow7_17_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_16 z * u6 z = pow7_17_q z * f z + pow7_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_17_mul_integer z


theorem pow7_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_16 z * u6 z = pow7_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_17_mul z


theorem pow7_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 17 = pow7_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow7_16_pow z hz]
  exact pow7_17_root z hz


def pow7_34 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (107 + z * (40 + z * (56 + z * (34 + z * (22 + z * (135 + z * (0 + z * (20 + z * (34 + z * (120 + z * (13 + z * (119 + z * (66 + z * (3 + z * (44 + z * (115 + z * (33 + z * (76 + z * 2)))))))))))))))))))

def pow7_34_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (131 + z * (58 + z * (116 + z * (82 + z * (57 + z * (98 + z * (9 + z * (40 + z * (8 + z * (79 + z * (14 + z * (3 + z * (102 + z * (0 + z * (34 + z * (85 + z * (7 + z * 25))))))))))))))))))

def pow7_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-75) + z * ((-180) + z * ((-187) + z * ((-337) + z * ((-234) + z * ((-320) + z * ((-179) + z * ((-219) + z * ((-190) + z * ((-119) + z * ((-300) + z * ((-157) + z * ((-74) + z * ((-296) + z * ((-15) + z * ((-127) + z * ((-75) + z * ((-63) + z * (39 + z * ((-229) + z * ((-62) + z * ((-24) + z * ((-24) + z * ((-58) + z * (28 + z * (30 + z * (9 + z * (118 + z * (103 + z * ((-119) + z * (110 + z * ((-71) + z * ((-94) + z * ((-31) + z * ((-69) + z * ((-82) + z * ((-20) + z * ((-23) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow7_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_17 z * pow7_17 z = pow7_34_q z * f z + pow7_34 z + (139 : R) * pow7_34_mul_t z := by
  simp only [pow7_17, pow7_34_q, f, pow7_34, pow7_34_mul_t]
  
  ring

theorem pow7_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_17 z * pow7_17 z = pow7_34_q z * f z + pow7_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_34_mul_integer z


theorem pow7_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_17 z * pow7_17 z = pow7_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_34_mul z


theorem pow7_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 34 = pow7_34 z := by
  calc
    _ = u6 z ^ 17 * u6 z ^ 17 := by ring
    _ = pow7_17 z * pow7_17 z := by rw [pow7_17_pow z hz]
    _ = _ := pow7_34_root z hz


def pow7_68 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (89 + z * (12 + z * (60 + z * (68 + z * (22 + z * (61 + z * (89 + z * (122 + z * (32 + z * (81 + z * (90 + z * (12 + z * (87 + z * (25 + z * (92 + z * (73 + z * (135 + z * (19 + z * 66)))))))))))))))))))

def pow7_68_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (65 + z * (133 + z * (106 + z * (18 + z * (34 + z * (57 + z * (65 + z * (43 + z * (23 + z * (88 + z * (10 + z * (134 + z * (76 + z * (123 + z * (30 + z * (15 + z * (70 + z * 4))))))))))))))))))

def pow7_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-66) + z * ((-147) + z * ((-259) + z * ((-254) + z * ((-247) + z * ((-171) + z * ((-109) + z * ((-247) + z * ((-268) + z * ((-322) + z * ((-226) + z * ((-225) + z * ((-282) + z * ((-369) + z * ((-483) + z * ((-300) + z * ((-362) + z * ((-211) + z * ((-249) + z * ((-347) + z * ((-367) + z * ((-63) + z * ((-239) + z * ((-92) + z * ((-176) + z * ((-131) + z * ((-186) + z * (28 + z * ((-90) + z * ((-122) + z * ((-97) + z * ((-99) + z * ((-94) + z * (92 + z * ((-26) + z * ((-25) + z * ((-2) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow7_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_34 z * pow7_34 z = pow7_68_q z * f z + pow7_68 z + (139 : R) * pow7_68_mul_t z := by
  simp only [pow7_34, pow7_68_q, f, pow7_68, pow7_68_mul_t]
  
  ring

theorem pow7_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_34 z * pow7_34 z = pow7_68_q z * f z + pow7_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_68_mul_integer z


theorem pow7_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_34 z * pow7_34 z = pow7_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_68_mul z


theorem pow7_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 68 = pow7_68 z := by
  calc
    _ = u6 z ^ 34 * u6 z ^ 34 := by ring
    _ = pow7_34 z * pow7_34 z := by rw [pow7_34_pow z hz]
    _ = _ := pow7_68_root z hz


def pow7_69 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (90 + z * (125 + z * (80 + z * (53 + z * (20 + z * (54 + z * (40 + z * (43 + z * (47 + z * (134 + z * (69 + z * (110 + z * (103 + z * (135 + z * (43 + z * (62 + z * (71 + z * (55 + z * 74)))))))))))))))))))

def pow7_69_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (20 + z * (93 + z * (84 + z * (2 + z * (134 + z * (80 + z * (93 + z * (65 + z * (38 + z * (73 + z * (4 + z * (60 + z * (29 + z * (107 + z * (101 + z * (61 + z * (123 + z * 41))))))))))))))))))

def pow7_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-58) + z * ((-8) + z * ((-108) + z * ((-228) + z * ((-196) + z * ((-127) + z * ((-164) + z * ((-166) + z * ((-192) + z * ((-183) + z * ((-277) + z * ((-168) + z * ((-174) + z * ((-153) + z * ((-182) + z * ((-316) + z * ((-273) + z * ((-173) + z * ((-379) + z * ((-352) + z * ((-180) + z * ((-353) + z * (5 + z * ((-152) + z * ((-61) + z * ((-184) + z * ((-33) + z * ((-176) + z * ((-90) + z * ((-79) + z * ((-147) + z * ((-83) + z * ((-53) + z * ((-93) + z * ((-21) + z * ((-10) + z * ((-78) + z * ((-3) + z * 13))))))))))))))))))))))))))))))))))))))

theorem pow7_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_68 z * u6 z = pow7_69_q z * f z + pow7_69 z + (139 : R) * pow7_69_mul_t z := by
  simp only [pow7_68, u6, pow7_69_q, f, pow7_69, pow7_69_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_68 z * u6 z = pow7_69_q z * f z + pow7_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_69_mul_integer z


theorem pow7_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_68 z * u6 z = pow7_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_69_mul z


theorem pow7_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 69 = pow7_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow7_68_pow z hz]
  exact pow7_69_root z hz


def pow7_138 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (102 + z * (112 + z * (11 + z * (42 + z * (65 + z * (49 + z * (48 + z * (115 + z * (33 + z * (65 + z * (95 + z * (37 + z * (64 + z * (31 + z * (77 + z * (28 + z * (116 + z * (133 + z * 8)))))))))))))))))))

def pow7_138_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (60 + z * (87 + z * (23 + z * (81 + z * (45 + z * (57 + z * (67 + z * (89 + z * (22 + z * (0 + z * (67 + z * (17 + z * (61 + z * (35 + z * (78 + z * (7 + z * (127 + z * 55))))))))))))))))))

def pow7_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (11 + z * (10 + z * (47 + z * (48 + z * (7 + z * ((-41) + z * ((-46) + z * ((-107) + z * ((-149) + z * ((-162) + z * ((-20) + z * (7 + z * (205 + z * (199 + z * (274 + z * (114 + z * (184 + z * (41 + z * (4 + z * (92 + z * (103 + z * (48 + z * (160 + z * (141 + z * (175 + z * (184 + z * (170 + z * (134 + z * (274 + z * (280 + z * (111 + z * (140 + z * (96 + z * (10 + z * (8 + z * (22 + z * ((-60) + z * (7 + z * 39))))))))))))))))))))))))))))))))))))))

theorem pow7_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_69 z * pow7_69 z = pow7_138_q z * f z + pow7_138 z + (139 : R) * pow7_138_mul_t z := by
  simp only [pow7_69, pow7_138_q, f, pow7_138, pow7_138_mul_t]
  
  ring

theorem pow7_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_69 z * pow7_69 z = pow7_138_q z * f z + pow7_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_138_mul_integer z


theorem pow7_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_69 z * pow7_69 z = pow7_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_138_mul z


theorem pow7_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 138 = pow7_138 z := by
  calc
    _ = u6 z ^ 69 * u6 z ^ 69 := by ring
    _ = pow7_69 z * pow7_69 z := by rw [pow7_69_pow z hz]
    _ = _ := pow7_138_root z hz


def pow7_139 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (104 + z * (88 + z * (36 + z * (41 + z * (102 + z * (131 + z * (65 + z * (132 + z * (82 + z * (40 + z * (63 + z * (28 + z * (122 + z * (71 + z * (6 + z * (113 + z * (125 + z * (130 + z * 57)))))))))))))))))))

def pow7_139_q {R : Type*} [CommRing R] (z : R) : R := (96 + z * (79 + z * (27 + z * (31 + z * (6 + z * (68 + z * (69 + z * (118 + z * (105 + z * (110 + z * (99 + z * (36 + z * (84 + z * (40 + z * (37 + z * (38 + z * (109 + z * (52 + z * 85))))))))))))))))))

def pow7_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-79) + z * ((-61) + z * ((-102) + z * ((-155) + z * ((-88) + z * ((-19) + z * ((-44) + z * ((-165) + z * ((-235) + z * ((-363) + z * ((-234) + z * ((-256) + z * ((-238) + z * ((-253) + z * ((-237) + z * ((-329) + z * ((-197) + z * ((-236) + z * ((-335) + z * ((-273) + z * ((-297) + z * ((-150) + z * ((-113) + z * ((-49) + z * ((-256) + z * ((-218) + z * ((-127) + z * ((-211) + z * ((-91) + z * ((-82) + z * ((-113) + z * ((-57) + z * (32 + z * ((-4) + z * ((-12) + z * ((-20) + z * ((-48) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow7_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_138 z * u6 z = pow7_139_q z * f z + pow7_139 z + (139 : R) * pow7_139_mul_t z := by
  simp only [pow7_138, u6, pow7_139_q, f, pow7_139, pow7_139_mul_t]
  simp only [pow6_139]
  ring

theorem pow7_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow7_138 z * u6 z = pow7_139_q z * f z + pow7_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow7_139_mul_integer z


theorem pow7_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow7_138 z * u6 z = pow7_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_139_mul z


theorem pow7_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u6 z ^ 139 = pow7_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow7_138_pow z hz]
  exact pow7_139_root z hz


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_139 z

theorem iterate7 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 7) = u7 z := by
  calc
    _ = (z ^ (139 ^ 6)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate6 z hz)
    _ = _ := pow7_139_pow z hz


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (49 + z * (22 + z * (135 + z * (107 + z * (117 + z * (129 + z * (71 + z * (42 + z * (102 + z * (136 + z * (79 + z * (21 + z * (98 + z * (126 + z * (111 + z * (104 + z * (41 + z * (62 + z * (47 + z * 10)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (31 + z * (35 + z * (54 + z * (37 + z * (40 + z * (109 + z * (110 + z * (138 + z * (6 + z * (68 + z * (66 + z * (86 + z * (87 + z * (86 + z * (111 + z * (2 + z * (102 + z * 52))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (39 + z * (55 + z * ((-34) + z * ((-62) + z * (74 + z * (156 + z * (71 + z * (70 + z * (8 + z * ((-59) + z * (52 + z * (0 + z * (60 + z * (114 + z * ((-159) + z * ((-122) + z * (72 + z * (175 + z * (218 + z * (54 + z * ((-12) + z * (158 + z * (138 + z * (203 + z * (142 + z * (70 + z * (32 + z * ((-50) + z * (82 + z * (63 + z * (60 + z * (103 + z * ((-7) + z * (181 + z * (249 + z * (92 + z * (58 + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow8_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z + (139 : R) * pow8_2_mul_t z := by
  simp only [u7, pow8_2_q, f, pow8_2, pow8_2_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_2_mul_integer z


theorem pow8_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z * u7 z = pow8_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_2_mul z


theorem pow8_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 2 = pow8_2 z := by
  calc
    _ = u7 z ^ 1 * u7 z ^ 1 := by ring
    _ = u7 z * u7 z := by simp only [pow_one]
    _ = _ := pow8_2_root z hz


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (17 + z * (61 + z * (92 + z * (21 + z * (62 + z * (24 + z * (133 + z * (87 + z * (87 + z * (14 + z * (6 + z * (80 + z * (91 + z * (119 + z * (117 + z * (16 + z * (119 + z * (118 + z * 19)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (37 + z * (9 + z * (21 + z * (50 + z * (74 + z * (16 + z * (4 + z * (41 + z * (95 + z * (67 + z * (50 + z * (137 + z * (80 + z * (107 + z * (59 + z * (121 + z * (94 + z * 100))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-36) + z * ((-74) + z * ((-4) + z * ((-6) + z * (93 + z * (158 + z * (216 + z * (280 + z * (292 + z * (243 + z * (257 + z * (310 + z * (266 + z * (175 + z * (231 + z * (257 + z * (223 + z * (395 + z * (242 + z * (115 + z * (141 + z * (176 + z * (189 + z * (127 + z * ((-10) + z * ((-63) + z * ((-3) + z * ((-52) + z * ((-124) + z * ((-64) + z * ((-112) + z * ((-185) + z * ((-158) + z * ((-162) + z * ((-157) + z * ((-133) + z * ((-136) + z * ((-86) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z + (139 : R) * pow8_4_mul_t z := by
  simp only [pow8_2, pow8_4_q, f, pow8_4, pow8_4_mul_t]
  
  ring

theorem pow8_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_4_mul_integer z


theorem pow8_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_2 z * pow8_2 z = pow8_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_4_mul z


theorem pow8_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 4 = pow8_4 z := by
  calc
    _ = u7 z ^ 2 * u7 z ^ 2 := by ring
    _ = pow8_2 z * pow8_2 z := by rw [pow8_2_pow z hz]
    _ = _ := pow8_4_root z hz


def pow8_8 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (31 + z * (127 + z * (92 + z * (92 + z * (14 + z * (94 + z * (54 + z * (18 + z * (80 + z * (18 + z * (83 + z * (131 + z * (123 + z * (122 + z * (65 + z * (54 + z * (47 + z * (109 + z * 94)))))))))))))))))))

def pow8_8_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (48 + z * (59 + z * (138 + z * (77 + z * (87 + z * (12 + z * (49 + z * (16 + z * (60 + z * (103 + z * (36 + z * (71 + z * (49 + z * (23 + z * (128 + z * (125 + z * (115 + z * 83))))))))))))))))))

def pow8_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-95) + z * ((-111) + z * ((-190) + z * ((-277) + z * ((-241) + z * ((-262) + z * ((-194) + z * ((-136) + z * ((-127) + z * ((-165) + z * ((-234) + z * ((-224) + z * ((-392) + z * ((-138) + z * ((-101) + z * ((-242) + z * ((-195) + z * ((-406) + z * ((-444) + z * ((-104) + z * (10 + z * (16 + z * ((-103) + z * ((-11) + z * ((-65) + z * (0 + z * (68 + z * ((-157) + z * ((-22) + z * (52 + z * ((-7) + z * (154 + z * ((-6) + z * ((-118) + z * (6 + z * ((-35) + z * ((-45) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow8_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z + (139 : R) * pow8_8_mul_t z := by
  simp only [pow8_4, pow8_8_q, f, pow8_8, pow8_8_mul_t]
  
  ring

theorem pow8_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_4 z * pow8_4 z = pow8_8_q z * f z + pow8_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_8_mul_integer z


theorem pow8_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_4 z * pow8_4 z = pow8_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_8_mul z


theorem pow8_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 8 = pow8_8 z := by
  calc
    _ = u7 z ^ 4 * u7 z ^ 4 := by ring
    _ = pow8_4 z * pow8_4 z := by rw [pow8_4_pow z hz]
    _ = _ := pow8_8_root z hz


def pow8_16 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (88 + z * (123 + z * (69 + z * (24 + z * (29 + z * (86 + z * (65 + z * (53 + z * (103 + z * (68 + z * (79 + z * (3 + z * (133 + z * (1 + z * (38 + z * (68 + z * (118 + z * (119 + z * 133)))))))))))))))))))

def pow8_16_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (17 + z * (57 + z * (57 + z * (56 + z * (118 + z * (8 + z * (58 + z * (40 + z * (75 + z * (124 + z * (125 + z * (35 + z * (134 + z * (103 + z * (54 + z * (71 + z * (94 + z * 79))))))))))))))))))

def pow8_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (58 + z * ((-3) + z * (115 + z * (55 + z * (112 + z * ((-39) + z * (109 + z * ((-26) + z * ((-12) + z * (19 + z * ((-140) + z * ((-132) + z * ((-98) + z * ((-70) + z * ((-44) + z * (55 + z * (65 + z * ((-81) + z * ((-37) + z * ((-48) + z * ((-74) + z * ((-3) + z * (24 + z * ((-146) + z * ((-76) + z * (137 + z * ((-52) + z * (5 + z * (32 + z * ((-61) + z * (127 + z * (168 + z * (71 + z * (39 + z * (20 + z * (12 + z * (4 + z * (74 + z * 63))))))))))))))))))))))))))))))))))))))

theorem pow8_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z + (139 : R) * pow8_16_mul_t z := by
  simp only [pow8_8, pow8_16_q, f, pow8_16, pow8_16_mul_t]
  
  ring

theorem pow8_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_8 z * pow8_8 z = pow8_16_q z * f z + pow8_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_16_mul_integer z


theorem pow8_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_8 z * pow8_8 z = pow8_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_16_mul z


theorem pow8_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 16 = pow8_16 z := by
  calc
    _ = u7 z ^ 8 * u7 z ^ 8 := by ring
    _ = pow8_8 z * pow8_8 z := by rw [pow8_8_pow z hz]
    _ = _ := pow8_16_root z hz


def pow8_17 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (119 + z * (26 + z * (19 + z * (100 + z * (69 + z * (70 + z * (121 + z * (10 + z * (12 + z * (11 + z * (18 + z * (114 + z * (12 + z * (42 + z * (2 + z * (27 + z * (119 + z * (106 + z * 43)))))))))))))))))))

def pow8_17_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (127 + z * (133 + z * (64 + z * (107 + z * (57 + z * (126 + z * (112 + z * (46 + z * (111 + z * (58 + z * (54 + z * (101 + z * (0 + z * (70 + z * (66 + z * (83 + z * (17 + z * 75))))))))))))))))))

def pow8_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * ((-24) + z * ((-57) + z * ((-133) + z * ((-247) + z * ((-228) + z * ((-149) + z * ((-147) + z * ((-102) + z * ((-182) + z * ((-265) + z * ((-205) + z * ((-274) + z * ((-153) + z * ((-190) + z * ((-217) + z * ((-282) + z * ((-120) + z * (11 + z * (43 + z * ((-109) + z * ((-57) + z * ((-97) + z * (72 + z * (154 + z * ((-3) + z * (195 + z * (166 + z * ((-19) + z * (143 + z * (86 + z * (73 + z * (164 + z * (91 + z * (103 + z * (264 + z * (208 + z * (104 + z * 54))))))))))))))))))))))))))))))))))))))

theorem pow8_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_16 z * u7 z = pow8_17_q z * f z + pow8_17 z + (139 : R) * pow8_17_mul_t z := by
  simp only [pow8_16, u7, pow8_17_q, f, pow8_17, pow8_17_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_16 z * u7 z = pow8_17_q z * f z + pow8_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_17_mul_integer z


theorem pow8_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_16 z * u7 z = pow8_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_17_mul z


theorem pow8_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 17 = pow8_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow8_16_pow z hz]
  exact pow8_17_root z hz


def pow8_34 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (98 + z * (89 + z * (122 + z * (26 + z * (43 + z * (35 + z * (76 + z * (54 + z * (31 + z * (86 + z * (70 + z * (128 + z * (5 + z * (117 + z * (109 + z * (123 + z * (116 + z * (103 + z * 32)))))))))))))))))))

def pow8_34_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (113 + z * (44 + z * (113 + z * (138 + z * (62 + z * (100 + z * (67 + z * (137 + z * (87 + z * (59 + z * (0 + z * (9 + z * (95 + z * (2 + z * (65 + z * (85 + z * (126 + z * 42))))))))))))))))))

def pow8_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-84) + z * ((-129) + z * ((-129) + z * ((-290) + z * ((-355) + z * ((-221) + z * ((-276) + z * ((-295) + z * ((-272) + z * ((-478) + z * ((-561) + z * ((-401) + z * ((-341) + z * ((-381) + z * ((-454) + z * ((-505) + z * ((-618) + z * ((-614) + z * ((-417) + z * ((-486) + z * ((-539) + z * ((-337) + z * ((-371) + z * ((-272) + z * ((-75) + z * ((-234) + z * ((-349) + z * ((-371) + z * ((-232) + z * ((-47) + z * (8 + z * ((-117) + z * ((-178) + z * ((-107) + z * ((-13) + z * (27 + z * (7 + z * (26 + z * 13))))))))))))))))))))))))))))))))))))))

theorem pow8_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_17 z * pow8_17 z = pow8_34_q z * f z + pow8_34 z + (139 : R) * pow8_34_mul_t z := by
  simp only [pow8_17, pow8_34_q, f, pow8_34, pow8_34_mul_t]
  
  ring

theorem pow8_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_17 z * pow8_17 z = pow8_34_q z * f z + pow8_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_34_mul_integer z


theorem pow8_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_17 z * pow8_17 z = pow8_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_34_mul z


theorem pow8_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 34 = pow8_34 z := by
  calc
    _ = u7 z ^ 17 * u7 z ^ 17 := by ring
    _ = pow8_17 z * pow8_17 z := by rw [pow8_17_pow z hz]
    _ = _ := pow8_34_root z hz


def pow8_68 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (93 + z * (37 + z * (136 + z * (101 + z * (45 + z * (94 + z * (86 + z * (9 + z * (89 + z * (54 + z * (98 + z * (11 + z * (102 + z * (70 + z * (60 + z * (124 + z * (56 + z * (135 + z * 137)))))))))))))))))))

def pow8_68_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (74 + z * (133 + z * (13 + z * (43 + z * (81 + z * (19 + z * (46 + z * (44 + z * (127 + z * (74 + z * (114 + z * (54 + z * (10 + z * (33 + z * (97 + z * (52 + z * (64 + z * 51))))))))))))))))))

def pow8_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-56) + z * ((-63) + z * ((-115) + z * ((-59) + z * ((-75) + z * ((-95) + z * ((-69) + z * ((-81) + z * ((-73) + z * ((-213) + z * ((-209) + z * ((-244) + z * ((-168) + z * ((-116) + z * ((-71) + z * ((-48) + z * ((-37) + z * (185 + z * (24 + z * (89 + z * (4 + z * (22 + z * (153 + z * (54 + z * (53 + z * (19 + z * (239 + z * (107 + z * (187 + z * (251 + z * (194 + z * (208 + z * (327 + z * (233 + z * (159 + z * (133 + z * (33 + z * (0 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow8_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_34 z * pow8_34 z = pow8_68_q z * f z + pow8_68 z + (139 : R) * pow8_68_mul_t z := by
  simp only [pow8_34, pow8_68_q, f, pow8_68, pow8_68_mul_t]
  
  ring

theorem pow8_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_34 z * pow8_34 z = pow8_68_q z * f z + pow8_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_68_mul_integer z


theorem pow8_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_34 z * pow8_34 z = pow8_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_68_mul z


theorem pow8_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 68 = pow8_68 z := by
  calc
    _ = u7 z ^ 34 * u7 z ^ 34 := by ring
    _ = pow8_34 z * pow8_34 z := by rw [pow8_34_pow z hz]
    _ = _ := pow8_68_root z hz


def pow8_69 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (76 + z * (3 + z * (88 + z * (8 + z * (46 + z * (131 + z * (17 + z * (90 + z * (13 + z * (42 + z * (30 + z * (106 + z * (87 + z * (104 + z * (120 + z * (45 + z * (5 + z * (136 + z * 63)))))))))))))))))))

def pow8_69_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (86 + z * (127 + z * (99 + z * (102 + z * (100 + z * (111 + z * (43 + z * (20 + z * (72 + z * (116 + z * (75 + z * (44 + z * (84 + z * (41 + z * (105 + z * (31 + z * (65 + z * 25))))))))))))))))))

def pow8_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-53) + z * ((-59) + z * ((-153) + z * ((-169) + z * ((-209) + z * ((-205) + z * ((-185) + z * ((-155) + z * ((-121) + z * ((-74) + z * ((-223) + z * ((-108) + z * ((-157) + z * ((-276) + z * ((-173) + z * ((-231) + z * ((-179) + z * ((-15) + z * ((-73) + z * (31 + z * (92 + z * (92 + z * (146 + z * (127 + z * (207 + z * (99 + z * (139 + z * (270 + z * (43 + z * (108 + z * (120 + z * (131 + z * (268 + z * (132 + z * (166 + z * (259 + z * (194 + z * (160 + z * 56))))))))))))))))))))))))))))))))))))))

theorem pow8_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_68 z * u7 z = pow8_69_q z * f z + pow8_69 z + (139 : R) * pow8_69_mul_t z := by
  simp only [pow8_68, u7, pow8_69_q, f, pow8_69, pow8_69_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_68 z * u7 z = pow8_69_q z * f z + pow8_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_69_mul_integer z


theorem pow8_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_68 z * u7 z = pow8_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_69_mul z


theorem pow8_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 69 = pow8_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow8_68_pow z hz]
  exact pow8_69_root z hz


def pow8_138 {R : Type*} [CommRing R] (z : R) : R := (137 + z * (27 + z * (75 + z * (37 + z * (65 + z * (16 + z * (138 + z * (73 + z * (134 + z * (128 + z * (80 + z * (59 + z * (1 + z * (34 + z * (49 + z * (58 + z * (117 + z * (133 + z * (79 + z * 60)))))))))))))))))))

def pow8_138_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (77 + z * (66 + z * (19 + z * (51 + z * (24 + z * (36 + z * (116 + z * (106 + z * (130 + z * (73 + z * (48 + z * (93 + z * (54 + z * (43 + z * (99 + z * (29 + z * (52 + z * 77))))))))))))))))))

def pow8_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (68 + z * ((-87) + z * (9 + z * ((-91) + z * ((-110) + z * (157 + z * ((-74) + z * ((-108) + z * ((-172) + z * ((-411) + z * ((-298) + z * ((-182) + z * ((-129) + z * ((-80) + z * ((-100) + z * ((-203) + z * ((-417) + z * ((-2) + z * ((-94) + z * ((-198) + z * ((-44) + z * ((-222) + z * ((-196) + z * (32 + z * ((-180) + z * ((-30) + z * ((-61) + z * ((-98) + z * (66 + z * (120 + z * (31 + z * (134 + z * (127 + z * (20 + z * ((-15) + z * (33 + z * (52 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow8_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_69 z * pow8_69 z = pow8_138_q z * f z + pow8_138 z + (139 : R) * pow8_138_mul_t z := by
  simp only [pow8_69, pow8_138_q, f, pow8_138, pow8_138_mul_t]
  
  ring

theorem pow8_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_69 z * pow8_69 z = pow8_138_q z * f z + pow8_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_138_mul_integer z


theorem pow8_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_69 z * pow8_69 z = pow8_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_138_mul z


theorem pow8_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 138 = pow8_138 z := by
  calc
    _ = u7 z ^ 69 * u7 z ^ 69 := by ring
    _ = pow8_69 z * pow8_69 z := by rw [pow8_69_pow z hz]
    _ = _ := pow8_138_root z hz


def pow8_139 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (122 + z * (58 + z * (6 + z * (73 + z * (55 + z * (45 + z * (68 + z * (87 + z * (137 + z * (102 + z * (39 + z * (90 + z * (70 + z * (61 + z * (46 + z * (83 + z * (124 + z * (34 + z * 84)))))))))))))))))))

def pow8_139_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (82 + z * (28 + z * (83 + z * (128 + z * (34 + z * (114 + z * (82 + z * (75 + z * (80 + z * (130 + z * (116 + z * (110 + z * (15 + z * (22 + z * (48 + z * (67 + z * (22 + z * 84))))))))))))))))))

def pow8_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (43 + z * (58 + z * ((-42) + z * ((-112) + z * ((-97) + z * ((-11) + z * ((-80) + z * (65 + z * (38 + z * ((-86) + z * ((-138) + z * ((-210) + z * ((-189) + z * ((-120) + z * ((-28) + z * (16 + z * (107 + z * (86 + z * ((-75) + z * ((-138) + z * ((-33) + z * (33 + z * (130 + z * (200 + z * (80 + z * (98 + z * (119 + z * ((-28) + z * ((-8) + z * (11 + z * ((-6) + z * (170 + z * (194 + z * (156 + z * (214 + z * (100 + z * (11 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow8_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_138 z * u7 z = pow8_139_q z * f z + pow8_139 z + (139 : R) * pow8_139_mul_t z := by
  simp only [pow8_138, u7, pow8_139_q, f, pow8_139, pow8_139_mul_t]
  simp only [pow7_139]
  ring

theorem pow8_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow8_138 z * u7 z = pow8_139_q z * f z + pow8_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow8_139_mul_integer z


theorem pow8_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow8_138 z * u7 z = pow8_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_139_mul z


theorem pow8_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u7 z ^ 139 = pow8_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow8_138_pow z hz]
  exact pow8_139_root z hz


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_139 z

theorem iterate8 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 8) = u8 z := by
  calc
    _ = (z ^ (139 ^ 7)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u7 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate7 z hz)
    _ = _ := pow8_139_pow z hz

end DimensionTen.Mod139

end

end OAI
