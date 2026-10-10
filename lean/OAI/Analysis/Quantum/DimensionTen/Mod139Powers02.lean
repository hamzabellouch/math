import OAI.Analysis.Quantum.DimensionTen.Mod139Powers01

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow3_2 {R : Type*} [CommRing R] (z : R) : R := (119 + z * (31 + z * (110 + z * (57 + z * (41 + z * (15 + z * (21 + z * (60 + z * (98 + z * (111 + z * (50 + z * (134 + z * (125 + z * (18 + z * (118 + z * (67 + z * (27 + z * (7 + z * (65 + z * 97)))))))))))))))))))

def pow3_2_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (89 + z * (122 + z * (111 + z * (57 + z * (55 + z * (69 + z * (5 + z * (18 + z * (69 + z * (37 + z * (104 + z * (19 + z * (135 + z * (38 + z * (10 + z * (112 + z * (109 + z * 29))))))))))))))))))

def pow3_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-85) + z * ((-160) + z * ((-250) + z * ((-351) + z * ((-391) + z * ((-356) + z * ((-331) + z * ((-317) + z * ((-271) + z * ((-280) + z * ((-315) + z * ((-365) + z * ((-337) + z * ((-352) + z * ((-322) + z * ((-366) + z * ((-353) + z * ((-199) + z * ((-359) + z * ((-443) + z * ((-190) + z * ((-155) + z * ((-122) + z * (12 + z * (61 + z * (9 + z * ((-118) + z * ((-25) + z * (108 + z * ((-112) + z * ((-100) + z * ((-12) + z * ((-160) + z * ((-78) + z * ((-13) + z * ((-106) + z * ((-113) + z * ((-13) + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow3_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z + (139 : R) * pow3_2_mul_t z := by
  simp only [u2, pow3_2_q, f, pow3_2, pow3_2_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_2_mul_integer z


theorem pow3_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z * u2 z = pow3_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_2_mul z


theorem pow3_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 2 = pow3_2 z := by
  calc
    _ = u2 z ^ 1 * u2 z ^ 1 := by ring
    _ = u2 z * u2 z := by simp only [pow_one]
    _ = _ := pow3_2_root z hz


def pow3_4 {R : Type*} [CommRing R] (z : R) : R := (74 + z * (103 + z * (33 + z * (24 + z * (131 + z * (70 + z * (27 + z * (103 + z * (101 + z * (17 + z * (85 + z * (43 + z * (27 + z * (54 + z * (100 + z * (65 + z * (8 + z * (120 + z * (87 + z * 107)))))))))))))))))))

def pow3_4_q {R : Type*} [CommRing R] (z : R) : R := (64 + z * (77 + z * (25 + z * (51 + z * (126 + z * (50 + z * (69 + z * (131 + z * (100 + z * (17 + z * (53 + z * (23 + z * (100 + z * (122 + z * (27 + z * (22 + z * (28 + z * (44 + z * 96))))))))))))))))))

def pow3_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (53 + z * ((-62) + z * (51 + z * ((-44) + z * ((-104) + z * ((-164) + z * ((-192) + z * ((-265) + z * ((-250) + z * ((-136) + z * ((-200) + z * (23 + z * (17 + z * ((-204) + z * ((-88) + z * ((-153) + z * ((-172) + z * ((-233) + z * ((-53) + z * ((-52) + z * ((-126) + z * (16 + z * ((-85) + z * (8 + z * (18 + z * ((-24) + z * (10 + z * (47 + z * (22 + z * (76 + z * (176 + z * ((-97) + z * ((-77) + z * (90 + z * ((-2) + z * ((-14) + z * ((-71) + z * (2 + z * 67))))))))))))))))))))))))))))))))))))))

theorem pow3_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z + (139 : R) * pow3_4_mul_t z := by
  simp only [pow3_2, pow3_4_q, f, pow3_4, pow3_4_mul_t]
  
  ring

theorem pow3_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_4_mul_integer z


theorem pow3_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_2 z * pow3_2 z = pow3_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_4_mul z


theorem pow3_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 4 = pow3_4 z := by
  calc
    _ = u2 z ^ 2 * u2 z ^ 2 := by ring
    _ = pow3_2 z * pow3_2 z := by rw [pow3_2_pow z hz]
    _ = _ := pow3_4_root z hz


def pow3_8 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (39 + z * (13 + z * (72 + z * (85 + z * (27 + z * (67 + z * (112 + z * (81 + z * (53 + z * (20 + z * (46 + z * (50 + z * (21 + z * (72 + z * (119 + z * (2 + z * (108 + z * (122 + z * 3)))))))))))))))))))

def pow3_8_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (16 + z * (112 + z * (119 + z * (16 + z * (106 + z * (108 + z * (105 + z * (134 + z * (4 + z * (130 + z * (98 + z * (95 + z * (90 + z * (62 + z * (93 + z * (75 + z * (136 + z * 51))))))))))))))))))

def pow3_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-46) + z * ((-1) + z * ((-88) + z * ((-235) + z * ((-138) + z * ((-74) + z * ((-235) + z * ((-252) + z * ((-130) + z * ((-256) + z * ((-411) + z * ((-247) + z * ((-325) + z * ((-505) + z * ((-288) + z * ((-384) + z * ((-594) + z * ((-435) + z * ((-353) + z * ((-339) + z * ((-411) + z * ((-393) + z * ((-130) + z * ((-183) + z * ((-248) + z * ((-180) + z * ((-321) + z * ((-150) + z * ((-116) + z * ((-129) + z * ((-208) + z * ((-95) + z * (21 + z * ((-23) + z * (30 + z * ((-7) + z * (76 + z * (86 + z * 82))))))))))))))))))))))))))))))))))))))

theorem pow3_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z + (139 : R) * pow3_8_mul_t z := by
  simp only [pow3_4, pow3_8_q, f, pow3_8, pow3_8_mul_t]
  
  ring

theorem pow3_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_4 z * pow3_4 z = pow3_8_q z * f z + pow3_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_8_mul_integer z


theorem pow3_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_4 z * pow3_4 z = pow3_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_8_mul z


theorem pow3_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 8 = pow3_8 z := by
  calc
    _ = u2 z ^ 4 * u2 z ^ 4 := by ring
    _ = pow3_4 z * pow3_4 z := by rw [pow3_4_pow z hz]
    _ = _ := pow3_8_root z hz


def pow3_16 {R : Type*} [CommRing R] (z : R) : R := (62 + z * (36 + z * (4 + z * (131 + z * (70 + z * (107 + z * (124 + z * (128 + z * (61 + z * (5 + z * (74 + z * (40 + z * (49 + z * (121 + z * (118 + z * (95 + z * (136 + z * (107 + z * (67 + z * 4)))))))))))))))))))

def pow3_16_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (77 + z * (81 + z * (67 + z * (102 + z * (85 + z * (61 + z * (104 + z * (6 + z * (72 + z * (12 + z * (92 + z * (47 + z * (125 + z * (99 + z * (106 + z * (125 + z * (136 + z * 9))))))))))))))))))

def pow3_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * ((-95) + z * ((-198) + z * ((-177) + z * ((-194) + z * ((-282) + z * ((-228) + z * ((-164) + z * ((-182) + z * ((-263) + z * ((-264) + z * ((-203) + z * ((-200) + z * ((-406) + z * ((-370) + z * ((-311) + z * ((-604) + z * ((-522) + z * ((-310) + z * ((-525) + z * ((-514) + z * ((-182) + z * ((-189) + z * ((-316) + z * ((-203) + z * ((-204) + z * ((-234) + z * ((-269) + z * ((-221) + z * ((-160) + z * ((-225) + z * ((-215) + z * ((-71) + z * ((-74) + z * ((-105) + z * ((-26) + z * ((-21) + z * ((-4) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow3_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z + (139 : R) * pow3_16_mul_t z := by
  simp only [pow3_8, pow3_16_q, f, pow3_16, pow3_16_mul_t]
  
  ring

theorem pow3_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_8 z * pow3_8 z = pow3_16_q z * f z + pow3_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_16_mul_integer z


theorem pow3_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_8 z * pow3_8 z = pow3_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_16_mul z


theorem pow3_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 16 = pow3_16 z := by
  calc
    _ = u2 z ^ 8 * u2 z ^ 8 := by ring
    _ = pow3_8 z * pow3_8 z := by rw [pow3_8_pow z hz]
    _ = _ := pow3_16_root z hz


def pow3_17 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (69 + z * (80 + z * (8 + z * (17 + z * (71 + z * (138 + z * (118 + z * (81 + z * (48 + z * (48 + z * (6 + z * (108 + z * (3 + z * (117 + z * (29 + z * (54 + z * (45 + z * (50 + z * 91)))))))))))))))))))

def pow3_17_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (47 + z * (38 + z * (95 + z * (41 + z * (19 + z * (82 + z * (81 + z * (29 + z * (51 + z * (99 + z * (104 + z * (110 + z * (4 + z * (67 + z * (42 + z * (31 + z * (121 + z * 73))))))))))))))))))

def pow3_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-32) + z * ((-52) + z * ((-84) + z * ((-162) + z * ((-150) + z * ((-111) + z * ((-153) + z * ((-160) + z * ((-49) + z * ((-128) + z * ((-213) + z * ((-170) + z * ((-182) + z * ((-205) + z * ((-168) + z * ((-9) + z * ((-77) + z * ((-100) + z * ((-57) + z * ((-109) + z * ((-120) + z * ((-74) + z * (44 + z * (120 + z * ((-5) + z * ((-33) + z * (57 + z * ((-59) + z * (25 + z * (130 + z * ((-49) + z * (13 + z * (78 + z * ((-49) + z * ((-11) + z * ((-44) + z * ((-115) + z * ((-42) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow3_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_16 z * u2 z = pow3_17_q z * f z + pow3_17 z + (139 : R) * pow3_17_mul_t z := by
  simp only [pow3_16, u2, pow3_17_q, f, pow3_17, pow3_17_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_16 z * u2 z = pow3_17_q z * f z + pow3_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_17_mul_integer z


theorem pow3_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_16 z * u2 z = pow3_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_17_mul z


theorem pow3_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 17 = pow3_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow3_16_pow z hz]
  exact pow3_17_root z hz


def pow3_34 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (81 + z * (125 + z * (62 + z * (31 + z * (20 + z * (114 + z * (47 + z * (42 + z * (137 + z * (104 + z * (89 + z * (138 + z * (18 + z * (24 + z * (97 + z * (109 + z * (43 + z * (76 + z * 63)))))))))))))))))))

def pow3_34_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (16 + z * (127 + z * (129 + z * (25 + z * (110 + z * (87 + z * (67 + z * (95 + z * (70 + z * (10 + z * (94 + z * (101 + z * (11 + z * (33 + z * (65 + z * (137 + z * (111 + z * 80))))))))))))))))))

def pow3_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (90 + z * (97 + z * (51 + z * ((-135) + z * ((-183) + z * ((-213) + z * ((-97) + z * (17 + z * ((-8) + z * ((-173) + z * ((-186) + z * ((-270) + z * ((-153) + z * ((-138) + z * (84 + z * ((-260) + z * ((-256) + z * ((-341) + z * ((-438) + z * ((-242) + z * ((-226) + z * ((-410) + z * ((-250) + z * ((-139) + z * ((-146) + z * ((-236) + z * ((-84) + z * ((-315) + z * ((-90) + z * ((-121) + z * ((-226) + z * ((-123) + z * ((-126) + z * ((-13) + z * ((-136) + z * ((-105) + z * ((-85) + z * ((-9) + z * 59))))))))))))))))))))))))))))))))))))))

theorem pow3_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_17 z * pow3_17 z = pow3_34_q z * f z + pow3_34 z + (139 : R) * pow3_34_mul_t z := by
  simp only [pow3_17, pow3_34_q, f, pow3_34, pow3_34_mul_t]
  
  ring

theorem pow3_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_17 z * pow3_17 z = pow3_34_q z * f z + pow3_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_34_mul_integer z


theorem pow3_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_17 z * pow3_17 z = pow3_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_34_mul z


theorem pow3_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 34 = pow3_34 z := by
  calc
    _ = u2 z ^ 17 * u2 z ^ 17 := by ring
    _ = pow3_17 z * pow3_17 z := by rw [pow3_17_pow z hz]
    _ = _ := pow3_34_root z hz


def pow3_68 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (33 + z * (31 + z * (10 + z * (73 + z * (20 + z * (6 + z * (71 + z * (58 + z * (126 + z * (4 + z * (101 + z * (6 + z * (118 + z * (102 + z * (127 + z * (69 + z * (75 + z * (42 + z * 112)))))))))))))))))))

def pow3_68_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (71 + z * (123 + z * (131 + z * (18 + z * (95 + z * (67 + z * (21 + z * (122 + z * (29 + z * (57 + z * (76 + z * (73 + z * (40 + z * (132 + z * (121 + z * (121 + z * (137 + z * 77))))))))))))))))))

def pow3_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-34) + z * ((-48) + z * ((-128) + z * ((-144) + z * ((-231) + z * ((-200) + z * ((-137) + z * ((-109) + z * ((-127) + z * ((-122) + z * ((-49) + z * (17 + z * ((-43) + z * ((-128) + z * ((-254) + z * ((-283) + z * ((-234) + z * ((-208) + z * ((-228) + z * ((-163) + z * ((-143) + z * ((-43) + z * ((-137) + z * ((-157) + z * ((-12) + z * ((-101) + z * ((-50) + z * (79 + z * ((-102) + z * ((-161) + z * ((-93) + z * ((-167) + z * ((-179) + z * ((-45) + z * ((-67) + z * ((-103) + z * ((-3) + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow3_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_34 z * pow3_34 z = pow3_68_q z * f z + pow3_68 z + (139 : R) * pow3_68_mul_t z := by
  simp only [pow3_34, pow3_68_q, f, pow3_68, pow3_68_mul_t]
  
  ring

theorem pow3_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_34 z * pow3_34 z = pow3_68_q z * f z + pow3_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_68_mul_integer z


theorem pow3_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_34 z * pow3_34 z = pow3_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_68_mul z


theorem pow3_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 68 = pow3_68 z := by
  calc
    _ = u2 z ^ 34 * u2 z ^ 34 := by ring
    _ = pow3_34 z * pow3_34 z := by rw [pow3_34_pow z hz]
    _ = _ := pow3_68_root z hz


def pow3_69 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (79 + z * (119 + z * (7 + z * (82 + z * (124 + z * (5 + z * (50 + z * (71 + z * (132 + z * (29 + z * (49 + z * (77 + z * (67 + z * (37 + z * (114 + z * (53 + z * (90 + z * (12 + z * 79)))))))))))))))))))

def pow3_69_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (132 + z * (23 + z * (63 + z * (133 + z * (99 + z * (82 + z * (80 + z * (108 + z * (77 + z * (104 + z * (121 + z * (99 + z * (19 + z * (83 + z * (26 + z * (76 + z * (11 + z * 98))))))))))))))))))

def pow3_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-101) + z * ((-205) + z * ((-234) + z * ((-289) + z * ((-376) + z * ((-349) + z * ((-374) + z * ((-466) + z * ((-497) + z * ((-490) + z * ((-594) + z * ((-612) + z * ((-508) + z * ((-626) + z * ((-643) + z * ((-549) + z * ((-472) + z * ((-429) + z * ((-505) + z * ((-555) + z * ((-440) + z * ((-279) + z * ((-233) + z * ((-122) + z * ((-129) + z * ((-126) + z * ((-73) + z * ((-23) + z * (17 + z * (28 + z * (8 + z * (36 + z * (70 + z * (13 + z * (10 + z * (40 + z * ((-41) + z * ((-59) + z * 42))))))))))))))))))))))))))))))))))))))

theorem pow3_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_68 z * u2 z = pow3_69_q z * f z + pow3_69 z + (139 : R) * pow3_69_mul_t z := by
  simp only [pow3_68, u2, pow3_69_q, f, pow3_69, pow3_69_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_68 z * u2 z = pow3_69_q z * f z + pow3_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_69_mul_integer z


theorem pow3_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_68 z * u2 z = pow3_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_69_mul z


theorem pow3_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 69 = pow3_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow3_68_pow z hz]
  exact pow3_69_root z hz


def pow3_138 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (32 + z * (40 + z * (137 + z * (110 + z * (20 + z * (63 + z * (103 + z * (69 + z * (50 + z * (129 + z * (4 + z * (50 + z * (83 + z * (73 + z * (118 + z * (43 + z * (9 + z * (123 + z * 115)))))))))))))))))))

def pow3_138_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (137 + z * (100 + z * (38 + z * (17 + z * (123 + z * (21 + z * (10 + z * (85 + z * (99 + z * (61 + z * (34 + z * (59 + z * (55 + z * (122 + z * (87 + z * (65 + z * (74 + z * 125))))))))))))))))))

def pow3_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (110 + z * (33 + z * (59 + z * ((-102) + z * ((-14) + z * ((-14) + z * ((-8) + z * (52 + z * ((-93) + z * (122 + z * ((-37) + z * ((-134) + z * ((-108) + z * (97 + z * ((-64) + z * ((-175) + z * ((-93) + z * (4 + z * ((-314) + z * ((-124) + z * ((-194) + z * ((-160) + z * ((-104) + z * ((-167) + z * ((-79) + z * ((-156) + z * ((-51) + z * ((-229) + z * ((-111) + z * ((-96) + z * ((-82) + z * ((-123) + z * ((-44) + z * ((-188) + z * ((-36) + z * ((-39) + z * ((-57) + z * ((-102) + z * 44))))))))))))))))))))))))))))))))))))))

theorem pow3_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_69 z * pow3_69 z = pow3_138_q z * f z + pow3_138 z + (139 : R) * pow3_138_mul_t z := by
  simp only [pow3_69, pow3_138_q, f, pow3_138, pow3_138_mul_t]
  
  ring

theorem pow3_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_69 z * pow3_69 z = pow3_138_q z * f z + pow3_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_138_mul_integer z


theorem pow3_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_69 z * pow3_69 z = pow3_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_138_mul z


theorem pow3_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 138 = pow3_138 z := by
  calc
    _ = u2 z ^ 69 * u2 z ^ 69 := by ring
    _ = pow3_69 z * pow3_69 z := by rw [pow3_69_pow z hz]
    _ = _ := pow3_138_root z hz


def pow3_139 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (84 + z * (22 + z * (94 + z * (42 + z * (86 + z * (71 + z * (70 + z * (0 + z * (20 + z * (72 + z * (135 + z * (38 + z * (47 + z * (74 + z * (60 + z * (0 + z * (25 + z * (35 + z * 29)))))))))))))))))))

def pow3_139_q {R : Type*} [CommRing R] (z : R) : R := (92 + z * (105 + z * (85 + z * (98 + z * (8 + z * (86 + z * (19 + z * (37 + z * (33 + z * (113 + z * (22 + z * (7 + z * (44 + z * (108 + z * (40 + z * (133 + z * (87 + z * (133 + z * 118))))))))))))))))))

def pow3_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-67) + z * ((-143) + z * ((-215) + z * ((-293) + z * ((-255) + z * ((-234) + z * ((-223) + z * ((-181) + z * ((-105) + z * ((-241) + z * ((-287) + z * ((-135) + z * ((-91) + z * ((-194) + z * ((-149) + z * ((-165) + z * ((-255) + z * ((-290) + z * ((-379) + z * ((-307) + z * ((-190) + z * ((-264) + z * ((-60) + z * (57 + z * ((-116) + z * ((-146) + z * ((-35) + z * ((-68) + z * ((-120) + z * ((-11) + z * ((-50) + z * ((-122) + z * ((-130) + z * ((-143) + z * ((-65) + z * ((-72) + z * ((-182) + z * ((-47) + z * 43))))))))))))))))))))))))))))))))))))))

theorem pow3_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_138 z * u2 z = pow3_139_q z * f z + pow3_139 z + (139 : R) * pow3_139_mul_t z := by
  simp only [pow3_138, u2, pow3_139_q, f, pow3_139, pow3_139_mul_t]
  simp only [pow2_139]
  ring

theorem pow3_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow3_138 z * u2 z = pow3_139_q z * f z + pow3_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow3_139_mul_integer z


theorem pow3_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow3_138 z * u2 z = pow3_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_139_mul z


theorem pow3_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u2 z ^ 139 = pow3_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow3_138_pow z hz]
  exact pow3_139_root z hz


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_139 z

theorem iterate3 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 3) = u3 z := by
  calc
    _ = (z ^ (139 ^ 2)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u2 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate2 z hz)
    _ = _ := pow3_139_pow z hz


def pow4_2 {R : Type*} [CommRing R] (z : R) : R := (101 + z * (106 + z * (23 + z * (122 + z * (23 + z * (102 + z * (102 + z * (59 + z * (21 + z * (15 + z * (113 + z * (31 + z * (51 + z * (64 + z * (1 + z * (115 + z * (122 + z * (49 + z * (73 + z * 104)))))))))))))))))))

def pow4_2_q {R : Type*} [CommRing R] (z : R) : R := (84 + z * (10 + z * (21 + z * (52 + z * (57 + z * (49 + z * (53 + z * (71 + z * (16 + z * (47 + z * (70 + z * (44 + z * (99 + z * (36 + z * (101 + z * (109 + z * (118 + z * (22 + z * 7))))))))))))))))))

def pow4_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-64) + z * ((-76) + z * ((-48) + z * ((-114) + z * ((-63) + z * ((-101) + z * ((-47) + z * ((-121) + z * ((-53) + z * ((-155) + z * ((-164) + z * ((-115) + z * ((-82) + z * ((-256) + z * ((-181) + z * ((-264) + z * ((-289) + z * ((-250) + z * ((-295) + z * ((-421) + z * ((-223) + z * ((-147) + z * ((-219) + z * ((-304) + z * ((-211) + z * ((-255) + z * ((-217) + z * ((-221) + z * ((-212) + z * ((-179) + z * ((-221) + z * ((-234) + z * ((-145) + z * ((-135) + z * ((-164) + z * ((-113) + z * ((-7) + z * (8 + z * 6))))))))))))))))))))))))))))))))))))))

theorem pow4_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z + (139 : R) * pow4_2_mul_t z := by
  simp only [u3, pow4_2_q, f, pow4_2, pow4_2_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_2_mul_integer z


theorem pow4_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z * u3 z = pow4_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_2_mul z


theorem pow4_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 2 = pow4_2 z := by
  calc
    _ = u3 z ^ 1 * u3 z ^ 1 := by ring
    _ = u3 z * u3 z := by simp only [pow_one]
    _ = _ := pow4_2_root z hz


def pow4_4 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (89 + z * (25 + z * (26 + z * (60 + z * (12 + z * (115 + z * (2 + z * (74 + z * (45 + z * (41 + z * (128 + z * (97 + z * (6 + z * (43 + z * (132 + z * (17 + z * (80 + z * (127 + z * 37)))))))))))))))))))

def pow4_4_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (50 + z * (92 + z * (116 + z * (137 + z * (10 + z * (44 + z * (4 + z * (23 + z * (117 + z * (7 + z * (65 + z * (101 + z * (63 + z * (54 + z * (83 + z * (100 + z * (25 + z * 113))))))))))))))))))

def pow4_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * (113 + z * ((-2) + z * ((-4) + z * ((-115) + z * ((-136) + z * (54 + z * ((-3) + z * (63 + z * ((-39) + z * (27 + z * ((-44) + z * ((-216) + z * ((-96) + z * ((-278) + z * ((-92) + z * (10 + z * ((-179) + z * ((-113) + z * ((-105) + z * ((-42) + z * ((-53) + z * ((-83) + z * ((-20) + z * ((-60) + z * ((-48) + z * (17 + z * ((-200) + z * ((-120) + z * (50 + z * ((-83) + z * ((-43) + z * (40 + z * (4 + z * (73 + z * (123 + z * (5 + z * (5 + z * 77))))))))))))))))))))))))))))))))))))))

theorem pow4_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z + (139 : R) * pow4_4_mul_t z := by
  simp only [pow4_2, pow4_4_q, f, pow4_4, pow4_4_mul_t]
  
  ring

theorem pow4_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_4_mul_integer z


theorem pow4_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_2 z * pow4_2 z = pow4_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_4_mul z


theorem pow4_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 4 = pow4_4 z := by
  calc
    _ = u3 z ^ 2 * u3 z ^ 2 := by ring
    _ = pow4_2 z * pow4_2 z := by rw [pow4_2_pow z hz]
    _ = _ := pow4_4_root z hz


def pow4_8 {R : Type*} [CommRing R] (z : R) : R := (103 + z * (8 + z * (46 + z * (20 + z * (134 + z * (19 + z * (65 + z * (101 + z * (28 + z * (83 + z * (93 + z * (38 + z * (47 + z * (1 + z * (113 + z * (45 + z * (109 + z * (135 + z * (100 + z * 113)))))))))))))))))))

def pow4_8_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (8 + z * (42 + z * (30 + z * (15 + z * (46 + z * (24 + z * (1 + z * (73 + z * (88 + z * (93 + z * (46 + z * (42 + z * (133 + z * (25 + z * (94 + z * (67 + z * (132 + z * 118))))))))))))))))))

def pow4_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-81) + z * ((-80) + z * ((-74) + z * ((-132) + z * ((-117) + z * ((-65) + z * ((-104) + z * ((-3) + z * ((-130) + z * ((-167) + z * ((-211) + z * ((-233) + z * ((-56) + z * ((-311) + z * ((-214) + z * ((-257) + z * ((-226) + z * ((-254) + z * ((-394) + z * ((-324) + z * ((-248) + z * ((-166) + z * ((-188) + z * ((-25) + z * ((-129) + z * ((-215) + z * ((-74) + z * ((-156) + z * ((-235) + z * (43 + z * (53 + z * ((-279) + z * ((-95) + z * (5 + z * ((-87) + z * ((-4) + z * ((-50) + z * ((-42) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow4_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z + (139 : R) * pow4_8_mul_t z := by
  simp only [pow4_4, pow4_8_q, f, pow4_8, pow4_8_mul_t]
  
  ring

theorem pow4_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_4 z * pow4_4 z = pow4_8_q z * f z + pow4_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_8_mul_integer z


theorem pow4_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_4 z * pow4_4 z = pow4_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_8_mul z


theorem pow4_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 8 = pow4_8 z := by
  calc
    _ = u3 z ^ 4 * u3 z ^ 4 := by ring
    _ = pow4_4 z * pow4_4 z := by rw [pow4_4_pow z hz]
    _ = _ := pow4_8_root z hz


def pow4_16 {R : Type*} [CommRing R] (z : R) : R := (95 + z * (119 + z * (38 + z * (78 + z * (26 + z * (13 + z * (107 + z * (113 + z * (43 + z * (99 + z * (73 + z * (57 + z * (108 + z * (22 + z * (122 + z * (0 + z * (67 + z * (92 + z * (46 + z * 65)))))))))))))))))))

def pow4_16_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (126 + z * (72 + z * (126 + z * (55 + z * (20 + z * (118 + z * (89 + z * (103 + z * (55 + z * (70 + z * (28 + z * (9 + z * (65 + z * (75 + z * (42 + z * (46 + z * (12 + z * 120))))))))))))))))))

def pow4_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (56 + z * ((-107) + z * ((-120) + z * ((-262) + z * ((-141) + z * ((-295) + z * ((-190) + z * ((-212) + z * ((-241) + z * ((-285) + z * ((-317) + z * ((-292) + z * ((-279) + z * ((-251) + z * ((-106) + z * ((-323) + z * ((-233) + z * ((-260) + z * ((-64) + z * ((-180) + z * ((-151) + z * (28 + z * ((-124) + z * (189 + z * (104 + z * (87 + z * (163 + z * (40 + z * (155 + z * (94 + z * (141 + z * (130 + z * (126 + z * (273 + z * (188 + z * (320 + z * (192 + z * (52 + z * 91))))))))))))))))))))))))))))))))))))))

theorem pow4_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z + (139 : R) * pow4_16_mul_t z := by
  simp only [pow4_8, pow4_16_q, f, pow4_16, pow4_16_mul_t]
  
  ring

theorem pow4_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_8 z * pow4_8 z = pow4_16_q z * f z + pow4_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_16_mul_integer z


theorem pow4_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_8 z * pow4_8 z = pow4_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_16_mul z


theorem pow4_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 16 = pow4_16 z := by
  calc
    _ = u3 z ^ 8 * u3 z ^ 8 := by ring
    _ = pow4_8 z * pow4_8 z := by rw [pow4_8_pow z hz]
    _ = _ := pow4_16_root z hz


def pow4_17 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (13 + z * (71 + z * (103 + z * (119 + z * (13 + z * (39 + z * (24 + z * (72 + z * (74 + z * (26 + z * (89 + z * (93 + z * (16 + z * (30 + z * (126 + z * (56 + z * (119 + z * (134 + z * 35)))))))))))))))))))

def pow4_17_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (116 + z * (93 + z * (101 + z * (124 + z * (73 + z * (24 + z * (120 + z * (69 + z * (93 + z * (46 + z * (21 + z * (55 + z * (57 + z * (76 + z * (76 + z * (102 + z * (19 + z * 78))))))))))))))))))

def pow4_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-98) + z * ((-158) + z * ((-232) + z * ((-278) + z * ((-310) + z * ((-224) + z * ((-244) + z * ((-288) + z * ((-366) + z * ((-359) + z * ((-299) + z * ((-189) + z * ((-236) + z * ((-289) + z * ((-258) + z * ((-490) + z * ((-384) + z * ((-401) + z * ((-403) + z * ((-323) + z * ((-204) + z * ((-289) + z * ((-260) + z * ((-127) + z * ((-177) + z * ((-229) + z * ((-141) + z * ((-146) + z * ((-76) + z * ((-66) + z * ((-141) + z * ((-117) + z * ((-100) + z * ((-149) + z * ((-63) + z * ((-33) + z * ((-46) + z * 13))))))))))))))))))))))))))))))))))))))

theorem pow4_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_16 z * u3 z = pow4_17_q z * f z + pow4_17 z + (139 : R) * pow4_17_mul_t z := by
  simp only [pow4_16, u3, pow4_17_q, f, pow4_17, pow4_17_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_16 z * u3 z = pow4_17_q z * f z + pow4_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_17_mul_integer z


theorem pow4_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_16 z * u3 z = pow4_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_17_mul z


theorem pow4_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 17 = pow4_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow4_16_pow z hz]
  exact pow4_17_root z hz


def pow4_34 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (31 + z * (84 + z * (107 + z * (77 + z * (31 + z * (104 + z * (130 + z * (137 + z * (18 + z * (57 + z * (6 + z * (30 + z * (128 + z * (60 + z * (120 + z * (74 + z * (66 + z * (132 + z * 48)))))))))))))))))))

def pow4_34_q {R : Type*} [CommRing R] (z : R) : R := (74 + z * (32 + z * (121 + z * (106 + z * (87 + z * (104 + z * (60 + z * (48 + z * (42 + z * (27 + z * (93 + z * (88 + z * (40 + z * (37 + z * (9 + z * (106 + z * (119 + z * (59 + z * 113))))))))))))))))))

def pow4_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-77) + z * ((-118) + z * ((-175) + z * ((-188) + z * ((-273) + z * ((-209) + z * ((-218) + z * ((-195) + z * ((-262) + z * ((-297) + z * ((-243) + z * ((-246) + z * ((-340) + z * ((-242) + z * ((-186) + z * ((-347) + z * ((-266) + z * ((-328) + z * ((-253) + z * ((-182) + z * ((-95) + z * ((-92) + z * ((-118) + z * ((-161) + z * ((-204) + z * ((-15) + z * (82 + z * ((-56) + z * (29 + z * (71 + z * ((-129) + z * (79 + z * (146 + z * ((-6) + z * (104 + z * (51 + z * ((-37) + z * 8))))))))))))))))))))))))))))))))))))))

theorem pow4_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_17 z * pow4_17 z = pow4_34_q z * f z + pow4_34 z + (139 : R) * pow4_34_mul_t z := by
  simp only [pow4_17, pow4_34_q, f, pow4_34, pow4_34_mul_t]
  
  ring

theorem pow4_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_17 z * pow4_17 z = pow4_34_q z * f z + pow4_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_34_mul_integer z


theorem pow4_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_17 z * pow4_17 z = pow4_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_34_mul z


theorem pow4_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 34 = pow4_34 z := by
  calc
    _ = u3 z ^ 17 * u3 z ^ 17 := by ring
    _ = pow4_17 z * pow4_17 z := by rw [pow4_17_pow z hz]
    _ = _ := pow4_34_root z hz


def pow4_68 {R : Type*} [CommRing R] (z : R) : R := (88 + z * (115 + z * (58 + z * (106 + z * (121 + z * (67 + z * (88 + z * (41 + z * (65 + z * (131 + z * (102 + z * (92 + z * (110 + z * (137 + z * (7 + z * (11 + z * (103 + z * (0 + z * (50 + z * 3)))))))))))))))))))

def pow4_68_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (58 + z * (130 + z * (56 + z * (6 + z * (126 + z * (51 + z * (111 + z * (53 + z * (44 + z * (52 + z * (2 + z * (7 + z * (136 + z * (31 + z * (59 + z * (96 + z * (69 + z * 80))))))))))))))))))

def pow4_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-63) + z * ((-121) + z * ((-175) + z * ((-190) + z * ((-153) + z * ((-165) + z * ((-88) + z * ((-100) + z * ((-74) + z * ((-126) + z * ((-35) + z * ((-59) + z * ((-66) + z * ((-66) + z * ((-22) + z * ((-80) + z * ((-99) + z * ((-104) + z * ((-126) + z * ((-31) + z * (75 + z * (226 + z * (224 + z * (121 + z * (104 + z * (157 + z * (47 + z * (6 + z * (48 + z * ((-13) + z * (155 + z * (128 + z * (50 + z * (158 + z * (63 + z * (37 + z * (48 + z * (17 + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow4_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_34 z * pow4_34 z = pow4_68_q z * f z + pow4_68 z + (139 : R) * pow4_68_mul_t z := by
  simp only [pow4_34, pow4_68_q, f, pow4_68, pow4_68_mul_t]
  
  ring

theorem pow4_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_34 z * pow4_34 z = pow4_68_q z * f z + pow4_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_68_mul_integer z


theorem pow4_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_34 z * pow4_34 z = pow4_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_68_mul z


theorem pow4_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 68 = pow4_68 z := by
  calc
    _ = u3 z ^ 34 * u3 z ^ 34 := by ring
    _ = pow4_34 z * pow4_34 z := by rw [pow4_34_pow z hz]
    _ = _ := pow4_68_root z hz


def pow4_69 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (105 + z * (48 + z * (126 + z * (69 + z * (40 + z * (72 + z * (26 + z * (104 + z * (63 + z * (98 + z * (123 + z * (66 + z * (35 + z * (110 + z * (60 + z * (67 + z * (114 + z * (101 + z * 41)))))))))))))))))))

def pow4_69_q {R : Type*} [CommRing R] (z : R) : R := (13 + z * (28 + z * (74 + z * (36 + z * (51 + z * (73 + z * (92 + z * (108 + z * (85 + z * (120 + z * (85 + z * (110 + z * (111 + z * (69 + z * (1 + z * (2 + z * (11 + z * (10 + z * 87))))))))))))))))))

def pow4_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * (24 + z * ((-7) + z * ((-14) + z * (8 + z * ((-8) + z * ((-17) + z * ((-26) + z * ((-135) + z * ((-202) + z * ((-193) + z * ((-182) + z * ((-215) + z * ((-203) + z * ((-75) + z * ((-87) + z * ((-67) + z * ((-62) + z * ((-165) + z * ((-127) + z * ((-253) + z * ((-276) + z * ((-224) + z * ((-54) + z * ((-127) + z * ((-289) + z * ((-223) + z * ((-149) + z * ((-212) + z * ((-93) + z * ((-73) + z * ((-127) + z * ((-57) + z * ((-21) + z * ((-53) + z * (13 + z * ((-60) + z * ((-69) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow4_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_68 z * u3 z = pow4_69_q z * f z + pow4_69 z + (139 : R) * pow4_69_mul_t z := by
  simp only [pow4_68, u3, pow4_69_q, f, pow4_69, pow4_69_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_68 z * u3 z = pow4_69_q z * f z + pow4_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_69_mul_integer z


theorem pow4_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_68 z * u3 z = pow4_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_69_mul z


theorem pow4_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 69 = pow4_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow4_68_pow z hz]
  exact pow4_69_root z hz


def pow4_138 {R : Type*} [CommRing R] (z : R) : R := (76 + z * (85 + z * (70 + z * (53 + z * (93 + z * (5 + z * (103 + z * (109 + z * (21 + z * (94 + z * (122 + z * (115 + z * (134 + z * (31 + z * (31 + z * (58 + z * (14 + z * (91 + z * (116 + z * 116)))))))))))))))))))

def pow4_138_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (119 + z * (72 + z * (25 + z * (23 + z * (25 + z * (30 + z * (97 + z * (89 + z * (14 + z * (133 + z * (81 + z * (7 + z * (64 + z * (21 + z * (128 + z * (115 + z * (85 + z * 13))))))))))))))))))

def pow4_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-58) + z * ((-104) + z * ((-135) + z * ((-123) + z * ((-40) + z * ((-34) + z * (56 + z * ((-2) + z * ((-107) + z * ((-42) + z * ((-212) + z * ((-64) + z * (80 + z * ((-1) + z * (59 + z * (1 + z * ((-132) + z * ((-72) + z * (39 + z * (39 + z * (52 + z * (179 + z * (282 + z * (19 + z * (52 + z * (89 + z * ((-23) + z * (182 + z * (216 + z * (40 + z * (47 + z * (46 + z * (81 + z * (69 + z * (13 + z * (36 + z * (52 + z * (47 + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow4_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_69 z * pow4_69 z = pow4_138_q z * f z + pow4_138 z + (139 : R) * pow4_138_mul_t z := by
  simp only [pow4_69, pow4_138_q, f, pow4_138, pow4_138_mul_t]
  
  ring

theorem pow4_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_69 z * pow4_69 z = pow4_138_q z * f z + pow4_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_138_mul_integer z


theorem pow4_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_69 z * pow4_69 z = pow4_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_138_mul z


theorem pow4_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 138 = pow4_138 z := by
  calc
    _ = u3 z ^ 69 * u3 z ^ 69 := by ring
    _ = pow4_69 z * pow4_69 z := by rw [pow4_69_pow z hz]
    _ = _ := pow4_138_root z hz


def pow4_139 {R : Type*} [CommRing R] (z : R) : R := (71 + z * (55 + z * (107 + z * (127 + z * (2 + z * (120 + z * (43 + z * (97 + z * (94 + z * (116 + z * (134 + z * (9 + z * (5 + z * (24 + z * (117 + z * (116 + z * (116 + z * (101 + z * (14 + z * 126)))))))))))))))))))

def pow4_139_q {R : Type*} [CommRing R] (z : R) : R := (134 + z * (135 + z * (28 + z * (123 + z * (133 + z * (30 + z * (5 + z * (136 + z * (116 + z * (31 + z * (28 + z * (106 + z * (49 + z * (79 + z * (88 + z * (29 + z * (55 + z * (87 + z * 28))))))))))))))))))

def pow4_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-99) + z * ((-171) + z * ((-195) + z * ((-258) + z * ((-340) + z * ((-239) + z * ((-206) + z * ((-216) + z * ((-316) + z * ((-330) + z * ((-374) + z * ((-309) + z * ((-172) + z * ((-260) + z * ((-335) + z * ((-213) + z * ((-396) + z * ((-399) + z * ((-292) + z * ((-398) + z * ((-283) + z * ((-129) + z * ((-108) + z * ((-165) + z * ((-30) + z * ((-17) + z * ((-248) + z * ((-266) + z * (24 + z * (8 + z * ((-66) + z * ((-59) + z * ((-86) + z * ((-58) + z * ((-9) + z * ((-68) + z * ((-32) + z * (27 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow4_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_138 z * u3 z = pow4_139_q z * f z + pow4_139 z + (139 : R) * pow4_139_mul_t z := by
  simp only [pow4_138, u3, pow4_139_q, f, pow4_139, pow4_139_mul_t]
  simp only [pow3_139]
  ring

theorem pow4_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow4_138 z * u3 z = pow4_139_q z * f z + pow4_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow4_139_mul_integer z


theorem pow4_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow4_138 z * u3 z = pow4_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_139_mul z


theorem pow4_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u3 z ^ 139 = pow4_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow4_138_pow z hz]
  exact pow4_139_root z hz


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_139 z

theorem iterate4 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 4) = u4 z := by
  calc
    _ = (z ^ (139 ^ 3)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u3 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate3 z hz)
    _ = _ := pow4_139_pow z hz

end DimensionTen.Mod139

end

end OAI
