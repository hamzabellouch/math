import OAI.Analysis.Quantum.DimensionTen.Mod139Model

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow1_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 1))

def pow1_2_q {R : Type*} [CommRing R] (_ : R) : R := 0

def pow1_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 0))

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (139 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


def pow1_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 1))))

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 0))))

theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (139 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


def pow1_8 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))

abbrev pow1_8_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))

theorem pow1_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z + (139 : R) * pow1_8_mul_t z := by
  simp only [pow1_4, pow1_8_q, f, pow1_8, pow1_8_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_8_mul_integer z


theorem pow1_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_4 z * pow1_4 z = pow1_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_8_mul z


theorem pow1_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 8 = pow1_8 z := by
  calc
    _ = u0 z ^ 4 * u0 z ^ 4 := by ring
    _ = pow1_4 z * pow1_4 z := by rw [pow1_4_pow z hz]
    _ = _ := pow1_8_root z hz


def pow1_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))))))))))

abbrev pow1_16_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))))))))))

theorem pow1_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z + (139 : R) * pow1_16_mul_t z := by
  simp only [pow1_8, pow1_16_q, f, pow1_16, pow1_16_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_16_mul_integer z


theorem pow1_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_8 z * pow1_8 z = pow1_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_16_mul z


theorem pow1_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 16 = pow1_16 z := by
  calc
    _ = u0 z ^ 8 * u0 z ^ 8 := by ring
    _ = pow1_8 z * pow1_8 z := by rw [pow1_8_pow z hz]
    _ = _ := pow1_16_root z hz


def pow1_17 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1)))))))))))))))))

abbrev pow1_17_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0)))))))))))))))))

theorem pow1_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z + (139 : R) * pow1_17_mul_t z := by
  simp only [pow1_16, u0, pow1_17_q, f, pow1_17, pow1_17_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_17_mul_integer z


theorem pow1_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_16 z * u0 z = pow1_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_17_mul z


theorem pow1_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 17 = pow1_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow1_16_pow z hz]
  exact pow1_17_root z hz


def pow1_34 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (57 + z * (122 + z * (89 + z * (70 + z * (31 + z * (109 + z * (36 + z * (76 + z * (24 + z * (69 + z * (127 + z * (118 + z * (80 + z * (50 + z * (34 + z * (12 + z * (90 + z * (71 + z * 50)))))))))))))))))))

def pow1_34_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (2 + z * (75 + z * (70 + z * (8 + z * (28 + z * (125 + z * (125 + z * (111 + z * (116 + z * (135 + z * (60 + z * (19 + z * (11 + z * 1))))))))))))))

def pow1_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-93) + z * ((-109) + z * ((-169) + z * ((-237) + z * ((-233) + z * ((-201) + z * ((-295) + z * ((-383) + z * ((-456) + z * ((-612) + z * ((-734) + z * ((-657) + z * ((-651) + z * ((-667) + z * ((-522) + z * ((-591) + z * ((-655) + z * ((-515) + z * ((-613) + z * ((-639) + z * ((-505) + z * ((-520) + z * ((-485) + z * ((-409) + z * ((-405) + z * ((-436) + z * ((-367) + z * ((-256) + z * ((-230) + z * ((-179) + z * ((-71) + z * ((-26) + z * ((-11) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))

theorem pow1_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z + (139 : R) * pow1_34_mul_t z := by
  simp only [pow1_17, pow1_34_q, f, pow1_34, pow1_34_mul_t]
  
  ring

theorem pow1_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_34_mul_integer z


theorem pow1_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_17 z * pow1_17 z = pow1_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_34_mul z


theorem pow1_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 34 = pow1_34 z := by
  calc
    _ = u0 z ^ 17 * u0 z ^ 17 := by ring
    _ = pow1_17 z * pow1_17 z := by rw [pow1_17_pow z hz]
    _ = _ := pow1_34_root z hz


def pow1_68 {R : Type*} [CommRing R] (z : R) : R := (106 + z * (39 + z * (2 + z * (92 + z * (90 + z * (63 + z * (33 + z * (65 + z * (127 + z * (100 + z * (47 + z * (1 + z * (86 + z * (25 + z * (59 + z * (0 + z * (94 + z * (130 + z * (2 + z * 87)))))))))))))))))))

def pow1_68_q {R : Type*} [CommRing R] (z : R) : R := (87 + z * (105 + z * (64 + z * (94 + z * (97 + z * (56 + z * (82 + z * (26 + z * (55 + z * (37 + z * (68 + z * (67 + z * (43 + z * (136 + z * (56 + z * (52 + z * (85 + z * (128 + z * 137))))))))))))))))))

def pow1_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (32 + z * ((-60) + z * (10 + z * ((-55) + z * ((-84) + z * ((-116) + z * ((-11) + z * ((-118) + z * ((-2) + z * ((-116) + z * ((-104) + z * ((-49) + z * (92 + z * ((-36) + z * (6 + z * ((-86) + z * ((-236) + z * ((-157) + z * ((-224) + z * ((-272) + z * ((-276) + z * ((-190) + z * ((-199) + z * ((-57) + z * ((-78) + z * ((-76) + z * ((-265) + z * ((-239) + z * ((-133) + z * ((-54) + z * ((-30) + z * ((-182) + z * ((-223) + z * ((-199) + z * ((-130) + z * ((-72) + z * ((-118) + z * ((-76) + z * 17))))))))))))))))))))))))))))))))))))))

theorem pow1_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z + (139 : R) * pow1_68_mul_t z := by
  simp only [pow1_34, pow1_68_q, f, pow1_68, pow1_68_mul_t]
  
  ring

theorem pow1_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_68_mul_integer z


theorem pow1_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_34 z * pow1_34 z = pow1_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_68_mul z


theorem pow1_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 68 = pow1_68 z := by
  calc
    _ = u0 z ^ 34 * u0 z ^ 34 := by ring
    _ = pow1_34 z * pow1_34 z := by rw [pow1_34_pow z hz]
    _ = _ := pow1_68_root z hz


def pow1_69 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (56 + z * (6 + z * (55 + z * (61 + z * (50 + z * (57 + z * (6 + z * (90 + z * (60 + z * (83 + z * (130 + z * (101 + z * (35 + z * (122 + z * (100 + z * (55 + z * (94 + z * (13 + z * 125)))))))))))))))))))

def pow1_69_q {R : Type*} [CommRing R] (_ : R) : R := 87

def pow1_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-76) + z * ((-78) + z * ((-83) + z * ((-68) + z * ((-26) + z * ((-30) + z * ((-48) + z * ((-49) + z * ((-74) + z * ((-85) + z * ((-20) + z * ((-22) + z * ((-81) + z * ((-37) + z * ((-56) + z * ((-73) + z * (0 + z * ((-63) + z * ((-81) + z * 0))))))))))))))))))))

theorem pow1_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z + (139 : R) * pow1_69_mul_t z := by
  simp only [pow1_68, u0, pow1_69_q, f, pow1_69, pow1_69_mul_t]
  
  ring

theorem pow1_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_69_mul_integer z


theorem pow1_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_68 z * u0 z = pow1_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_69_mul z


theorem pow1_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 69 = pow1_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow1_68_pow z hz]
  exact pow1_69_root z hz


def pow1_138 {R : Type*} [CommRing R] (z : R) : R := (132 + z * (136 + z * (31 + z * (133 + z * (59 + z * (108 + z * (31 + z * (22 + z * (29 + z * (29 + z * (82 + z * (17 + z * (54 + z * (43 + z * (44 + z * (72 + z * (111 + z * (42 + z * (73 + z * 106)))))))))))))))))))

def pow1_138_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (37 + z * (95 + z * (19 + z * (111 + z * (17 + z * (61 + z * (126 + z * (39 + z * (79 + z * (131 + z * (92 + z * (119 + z * (111 + z * (114 + z * (61 + z * (37 + z * (124 + z * 57))))))))))))))))))

def pow1_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-37) + z * ((-119) + z * ((-139) + z * ((-178) + z * ((-179) + z * ((-181) + z * ((-249) + z * ((-256) + z * ((-235) + z * ((-379) + z * ((-353) + z * ((-331) + z * ((-442) + z * ((-428) + z * ((-354) + z * ((-376) + z * ((-442) + z * ((-341) + z * ((-299) + z * ((-277) + z * ((-270) + z * ((-116) + z * ((-104) + z * ((-61) + z * ((-22) + z * ((-135) + z * (1 + z * (0 + z * (56 + z * (16 + z * (61 + z * ((-78) + z * (22 + z * (122 + z * ((-9) + z * (14 + z * ((-30) + z * 112))))))))))))))))))))))))))))))))))))))

theorem pow1_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z + (139 : R) * pow1_138_mul_t z := by
  simp only [pow1_69, pow1_138_q, f, pow1_138, pow1_138_mul_t]
  
  ring

theorem pow1_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_138_mul_integer z


theorem pow1_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_69 z * pow1_69 z = pow1_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_138_mul z


theorem pow1_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 138 = pow1_138 z := by
  calc
    _ = u0 z ^ 69 * u0 z ^ 69 := by ring
    _ = pow1_69 z * pow1_69 z := by rw [pow1_69_pow z hz]
    _ = _ := pow1_138_root z hz


def pow1_139 {R : Type*} [CommRing R] (z : R) : R := (129 + z * (127 + z * (91 + z * (78 + z * (116 + z * (55 + z * (24 + z * (70 + z * (94 + z * (64 + z * (69 + z * (132 + z * (27 + z * (35 + z * (11 + z * (62 + z * (8 + z * (111 + z * (72 + z * 127)))))))))))))))))))

def pow1_139_q {R : Type*} [CommRing R] (_ : R) : R := 106

def pow1_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-81) + z * ((-93) + z * ((-95) + z * ((-101) + z * ((-83) + z * ((-32) + z * ((-36) + z * ((-59) + z * ((-60) + z * ((-91) + z * ((-104) + z * ((-24) + z * ((-26) + z * ((-99) + z * ((-44) + z * ((-68) + z * ((-88) + z * (0 + z * ((-78) + z * ((-98) + z * 0))))))))))))))))))))

theorem pow1_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z + (139 : R) * pow1_139_mul_t z := by
  simp only [pow1_138, u0, pow1_139_q, f, pow1_139, pow1_139_mul_t]
  
  ring

theorem pow1_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_139_mul_integer z


theorem pow1_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_138 z * u0 z = pow1_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_139_mul z


theorem pow1_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 139 = pow1_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow1_138_pow z hz]
  exact pow1_139_root z hz


abbrev u1 {R : Type*} [CommRing R] (z : R) : R := pow1_139 z

theorem iterate1 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 1) = u1 z := by
  calc
    _ = (z ^ (139 ^ 0)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 139 := congrArg (fun x : R => x ^ 139) (initial z )
    _ = _ := pow1_139_pow z hz


def pow2_2 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (73 + z * (105 + z * (120 + z * (95 + z * (40 + z * (32 + z * (36 + z * (46 + z * (92 + z * (110 + z * (136 + z * (114 + z * (110 + z * (131 + z * (109 + z * (124 + z * (81 + z * (55 + z * 74)))))))))))))))))))

def pow2_2_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (118 + z * (53 + z * (5 + z * (103 + z * (25 + z * (75 + z * (116 + z * (18 + z * (23 + z * (85 + z * (10 + z * (49 + z * (118 + z * (51 + z * (138 + z * (9 + z * (134 + z * 5))))))))))))))))))

def pow2_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (125 + z * (119 + z * (131 + z * (156 + z * (152 + z * (79 + z * (28 + z * (106 + z * (123 + z * (38 + z * (227 + z * (290 + z * (72 + z * ((-138) + z * ((-43) + z * ((-223) + z * ((-240) + z * (108 + z * (197 + z * ((-37) + z * (156 + z * (44 + z * ((-118) + z * ((-53) + z * ((-169) + z * ((-32) + z * (51 + z * (47 + z * (3 + z * (47 + z * ((-203) + z * ((-67) + z * ((-167) + z * (72 + z * (22 + z * (113 + z * (126 + z * 116))))))))))))))))))))))))))))))))))))))

theorem pow2_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z + (139 : R) * pow2_2_mul_t z := by
  simp only [u1, pow2_2_q, f, pow2_2, pow2_2_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_2_mul_integer z


theorem pow2_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z * u1 z = pow2_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_2_mul z


theorem pow2_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 2 = pow2_2 z := by
  calc
    _ = u1 z ^ 1 * u1 z ^ 1 := by ring
    _ = u1 z * u1 z := by simp only [pow_one]
    _ = _ := pow2_2_root z hz


def pow2_4 {R : Type*} [CommRing R] (z : R) : R := (138 + z * (23 + z * (65 + z * (82 + z * (67 + z * (49 + z * (130 + z * (95 + z * (71 + z * (131 + z * (12 + z * (72 + z * (53 + z * (2 + z * (90 + z * (125 + z * (0 + z * (115 + z * (110 + z * 132)))))))))))))))))))

def pow2_4_q {R : Type*} [CommRing R] (z : R) : R := (117 + z * (97 + z * (121 + z * (91 + z * (31 + z * (10 + z * (7 + z * (57 + z * (114 + z * (49 + z * (100 + z * (109 + z * (60 + z * (11 + z * (5 + z * (85 + z * (97 + z * (127 + z * 55))))))))))))))))))

def pow2_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-90) + z * ((-120) + z * ((-122) + z * ((-79) + z * ((-15) + z * (33 + z * (6 + z * ((-91) + z * ((-145) + z * ((-197) + z * ((-104) + z * (37 + z * (182 + z * (343 + z * (307 + z * (267 + z * (220 + z * (123 + z * (171 + z * (182 + z * (212 + z * (384 + z * (389 + z * (329 + z * (363 + z * (314 + z * (385 + z * (479 + z * (405 + z * (306 + z * (254 + z * (259 + z * (162 + z * (66 + z * (13 + z * ((-50) + z * (7 + z * 39))))))))))))))))))))))))))))))))))))))

theorem pow2_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z + (139 : R) * pow2_4_mul_t z := by
  simp only [pow2_2, pow2_4_q, f, pow2_4, pow2_4_mul_t]
  
  ring

theorem pow2_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_4_mul_integer z


theorem pow2_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_2 z * pow2_2 z = pow2_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_4_mul z


theorem pow2_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 4 = pow2_4 z := by
  calc
    _ = u1 z ^ 2 * u1 z ^ 2 := by ring
    _ = pow2_2 z * pow2_2 z := by rw [pow2_2_pow z hz]
    _ = _ := pow2_4_root z hz


def pow2_8 {R : Type*} [CommRing R] (z : R) : R := (76 + z * (10 + z * (97 + z * (94 + z * (37 + z * (77 + z * (14 + z * (129 + z * (3 + z * (63 + z * (58 + z * (14 + z * (55 + z * (108 + z * (68 + z * (18 + z * (54 + z * (79 + z * (56 + z * 109)))))))))))))))))))

def pow2_8_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (68 + z * (31 + z * (48 + z * (118 + z * (60 + z * (18 + z * (83 + z * (5 + z * (47 + z * (33 + z * (12 + z * (13 + z * (57 + z * (61 + z * (112 + z * (41 + z * (111 + z * 49))))))))))))))))))

def pow2_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * ((-40) + z * (14 + z * (22 + z * ((-64) + z * ((-91) + z * (109 + z * (19 + z * (57 + z * (253 + z * (25 + z * (166 + z * (226 + z * (41 + z * (133 + z * (281 + z * ((-90) + z * (88 + z * (194 + z * (101 + z * (95 + z * (378 + z * (156 + z * (244 + z * (328 + z * (214 + z * (331 + z * (134 + z * (121 + z * (137 + z * (60 + z * ((-13) + z * (130 + z * (106 + z * (158 + z * (62 + z * (167 + z * (163 + z * 125))))))))))))))))))))))))))))))))))))))

theorem pow2_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z + (139 : R) * pow2_8_mul_t z := by
  simp only [pow2_4, pow2_8_q, f, pow2_8, pow2_8_mul_t]
  
  ring

theorem pow2_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_4 z * pow2_4 z = pow2_8_q z * f z + pow2_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_8_mul_integer z


theorem pow2_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_4 z * pow2_4 z = pow2_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_8_mul z


theorem pow2_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 8 = pow2_8 z := by
  calc
    _ = u1 z ^ 4 * u1 z ^ 4 := by ring
    _ = pow2_4 z * pow2_4 z := by rw [pow2_4_pow z hz]
    _ = _ := pow2_8_root z hz


def pow2_16 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (88 + z * (64 + z * (53 + z * (96 + z * (27 + z * (52 + z * (57 + z * (82 + z * (67 + z * (19 + z * (80 + z * (56 + z * (82 + z * (108 + z * (51 + z * (53 + z * (59 + z * (100 + z * 74)))))))))))))))))))

def pow2_16_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (71 + z * (45 + z * (2 + z * (21 + z * (37 + z * (108 + z * (20 + z * (21 + z * (83 + z * (43 + z * (5 + z * (26 + z * (74 + z * (129 + z * (86 + z * (81 + z * (7 + z * 66))))))))))))))))))

def pow2_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-139) + z * ((-88) + z * ((-92) + z * ((-90) + z * (41 + z * ((-88) + z * (37 + z * ((-144) + z * ((-87) + z * ((-139) + z * ((-143) + z * (52 + z * ((-146) + z * ((-98) + z * ((-269) + z * ((-235) + z * ((-151) + z * ((-259) + z * ((-130) + z * ((-27) + z * (62 + z * ((-52) + z * ((-57) + z * ((-104) + z * ((-186) + z * (136 + z * ((-103) + z * ((-132) + z * ((-50) + z * (1 + z * ((-2) + z * (3 + z * ((-48) + z * ((-78) + z * (68 + z * (91 + z * (27 + z * 85))))))))))))))))))))))))))))))))))))))

theorem pow2_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z + (139 : R) * pow2_16_mul_t z := by
  simp only [pow2_8, pow2_16_q, f, pow2_16, pow2_16_mul_t]
  
  ring

theorem pow2_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_8 z * pow2_8 z = pow2_16_q z * f z + pow2_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_16_mul_integer z


theorem pow2_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_8 z * pow2_8 z = pow2_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_16_mul z


theorem pow2_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 16 = pow2_16 z := by
  calc
    _ = u1 z ^ 8 * u1 z ^ 8 := by ring
    _ = pow2_8 z * pow2_8 z := by rw [pow2_8_pow z hz]
    _ = _ := pow2_16_root z hz


def pow2_17 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (75 + z * (15 + z * (125 + z * (114 + z * (122 + z * (34 + z * (47 + z * (96 + z * (130 + z * (53 + z * (87 + z * (114 + z * (41 + z * (79 + z * (44 + z * (90 + z * (109 + z * (86 + z * 41)))))))))))))))))))

def pow2_17_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (60 + z * (42 + z * (31 + z * (60 + z * (77 + z * (49 + z * (85 + z * (108 + z * (43 + z * (9 + z * (32 + z * (114 + z * (63 + z * (88 + z * (116 + z * (13 + z * (59 + z * 85))))))))))))))))))

def pow2_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-7) + z * (3 + z * ((-9) + z * (23 + z * (18 + z * ((-8) + z * ((-64) + z * ((-69) + z * ((-87) + z * ((-115) + z * ((-5) + z * (31 + z * ((-43) + z * ((-94) + z * ((-162) + z * ((-203) + z * ((-157) + z * ((-114) + z * (11 + z * ((-19) + z * ((-88) + z * ((-58) + z * ((-42) + z * ((-124) + z * ((-63) + z * ((-13) + z * ((-128) + z * ((-81) + z * (82 + z * ((-37) + z * ((-110) + z * (20 + z * ((-49) + z * ((-28) + z * (107 + z * (48 + z * (51 + z * 67))))))))))))))))))))))))))))))))))))))

theorem pow2_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_16 z * u1 z = pow2_17_q z * f z + pow2_17 z + (139 : R) * pow2_17_mul_t z := by
  simp only [pow2_16, u1, pow2_17_q, f, pow2_17, pow2_17_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_16 z * u1 z = pow2_17_q z * f z + pow2_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_17_mul_integer z


theorem pow2_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_16 z * u1 z = pow2_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_17_mul z


theorem pow2_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 17 = pow2_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow2_16_pow z hz]
  exact pow2_17_root z hz


def pow2_34 {R : Type*} [CommRing R] (z : R) : R := (8 + z * (115 + z * (17 + z * (4 + z * (120 + z * (38 + z * (66 + z * (68 + z * (80 + z * (64 + z * (58 + z * (42 + z * (13 + z * (69 + z * (68 + z * (60 + z * (80 + z * (44 + z * (93 + z * 9)))))))))))))))))))

def pow2_34_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (51 + z * (39 + z * (115 + z * (68 + z * (33 + z * (47 + z * (115 + z * (25 + z * (78 + z * (45 + z * (79 + z * (48 + z * (0 + z * (117 + z * (20 + z * (50 + z * (106 + z * 13))))))))))))))))))

def pow2_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-56) + z * ((-70) + z * ((-116) + z * ((-148) + z * ((-89) + z * ((-47) + z * ((-21) + z * ((-94) + z * (67 + z * (26 + z * ((-85) + z * ((-52) + z * (160 + z * (76 + z * (82 + z * (114 + z * (24 + z * (168 + z * (82 + z * (83 + z * (249 + z * (332 + z * (243 + z * (231 + z * (136 + z * (142 + z * (203 + z * (114 + z * (236 + z * (162 + z * (31 + z * (149 + z * (48 + z * (23 + z * (156 + z * (64 + z * (10 + z * (38 + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow2_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_17 z * pow2_17 z = pow2_34_q z * f z + pow2_34 z + (139 : R) * pow2_34_mul_t z := by
  simp only [pow2_17, pow2_34_q, f, pow2_34, pow2_34_mul_t]
  
  ring

theorem pow2_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_17 z * pow2_17 z = pow2_34_q z * f z + pow2_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_34_mul_integer z


theorem pow2_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_17 z * pow2_17 z = pow2_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_34_mul z


theorem pow2_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 34 = pow2_34 z := by
  calc
    _ = u1 z ^ 17 * u1 z ^ 17 := by ring
    _ = pow2_17 z * pow2_17 z := by rw [pow2_17_pow z hz]
    _ = _ := pow2_34_root z hz


def pow2_68 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (2 + z * (66 + z * (104 + z * (16 + z * (37 + z * (43 + z * (111 + z * (53 + z * (106 + z * (115 + z * (48 + z * (24 + z * (102 + z * (35 + z * (121 + z * (63 + z * (111 + z * (17 + z * 17)))))))))))))))))))

def pow2_68_q {R : Type*} [CommRing R] (z : R) : R := (97 + z * (16 + z * (19 + z * (30 + z * (87 + z * (76 + z * (41 + z * (86 + z * (112 + z * (75 + z * (105 + z * (18 + z * (80 + z * (22 + z * (16 + z * (21 + z * (65 + z * (63 + z * 81))))))))))))))))))

def pow2_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-73) + z * ((-84) + z * ((-19) + z * ((-118) + z * ((-178) + z * ((-17) + z * ((-158) + z * ((-208) + z * ((-173) + z * ((-245) + z * ((-289) + z * ((-230) + z * ((-237) + z * ((-332) + z * ((-180) + z * ((-151) + z * ((-253) + z * ((-162) + z * ((-316) + z * ((-243) + z * ((-242) + z * ((-195) + z * ((-65) + z * ((-177) + z * ((-77) + z * ((-151) + z * ((-180) + z * ((-140) + z * ((-143) + z * ((-32) + z * ((-38) + z * ((-45) + z * (23 + z * (5 + z * ((-6) + z * ((-37) + z * ((-50) + z * ((-63) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow2_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_34 z * pow2_34 z = pow2_68_q z * f z + pow2_68 z + (139 : R) * pow2_68_mul_t z := by
  simp only [pow2_34, pow2_68_q, f, pow2_68, pow2_68_mul_t]
  
  ring

theorem pow2_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_34 z * pow2_34 z = pow2_68_q z * f z + pow2_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_68_mul_integer z


theorem pow2_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_34 z * pow2_34 z = pow2_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_68_mul z


theorem pow2_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 68 = pow2_68 z := by
  calc
    _ = u1 z ^ 34 * u1 z ^ 34 := by ring
    _ = pow2_34 z * pow2_34 z := by rw [pow2_34_pow z hz]
    _ = _ := pow2_68_root z hz


def pow2_69 {R : Type*} [CommRing R] (z : R) : R := (134 + z * (79 + z * (128 + z * (91 + z * (11 + z * (53 + z * (66 + z * (33 + z * (85 + z * (88 + z * (83 + z * (33 + z * (46 + z * (116 + z * (22 + z * (33 + z * (81 + z * (64 + z * (13 + z * 133)))))))))))))))))))

def pow2_69_q {R : Type*} [CommRing R] (z : R) : R := (77 + z * (39 + z * (38 + z * (96 + z * (41 + z * (121 + z * (4 + z * (133 + z * (12 + z * (88 + z * (124 + z * (123 + z * (138 + z * (68 + z * (62 + z * (106 + z * (88 + z * (27 + z * 74))))))))))))))))))

def pow2_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-72) + z * ((-53) + z * ((-42) + z * ((-71) + z * ((-138) + z * ((-103) + z * ((-93) + z * ((-100) + z * ((-105) + z * ((-81) + z * ((-105) + z * ((-282) + z * ((-293) + z * ((-255) + z * ((-296) + z * ((-332) + z * ((-132) + z * ((-245) + z * ((-334) + z * ((-260) + z * ((-210) + z * ((-230) + z * ((-331) + z * ((-139) + z * ((-266) + z * ((-131) + z * ((-106) + z * ((-147) + z * ((-209) + z * ((-169) + z * ((-249) + z * (36 + z * ((-45) + z * (16 + z * (28 + z * (44 + z * ((-44) + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow2_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_68 z * u1 z = pow2_69_q z * f z + pow2_69 z + (139 : R) * pow2_69_mul_t z := by
  simp only [pow2_68, u1, pow2_69_q, f, pow2_69, pow2_69_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_68 z * u1 z = pow2_69_q z * f z + pow2_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_69_mul_integer z


theorem pow2_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_68 z * u1 z = pow2_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_69_mul z


theorem pow2_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 69 = pow2_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow2_68_pow z hz]
  exact pow2_69_root z hz


def pow2_138 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (35 + z * (0 + z * (119 + z * (137 + z * (72 + z * (104 + z * (136 + z * (30 + z * (78 + z * (43 + z * (28 + z * (43 + z * (130 + z * (71 + z * (104 + z * (52 + z * (20 + z * (41 + z * 71)))))))))))))))))))

def pow2_138_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (70 + z * (59 + z * (96 + z * (38 + z * (40 + z * (5 + z * (40 + z * (55 + z * (30 + z * (6 + z * (88 + z * (44 + z * (124 + z * (39 + z * (110 + z * (37 + z * (101 + z * 36))))))))))))))))))

def pow2_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (111 + z * (79 + z * (165 + z * (111 + z * ((-9) + z * (14 + z * (27 + z * (13 + z * (143 + z * (142 + z * (174 + z * (90 + z * (58 + z * (80 + z * ((-31) + z * ((-25) + z * ((-33) + z * ((-138) + z * ((-61) + z * (167 + z * ((-83) + z * ((-1) + z * (32 + z * ((-107) + z * ((-69) + z * (44 + z * ((-66) + z * ((-75) + z * ((-8) + z * (41 + z * ((-123) + z * ((-155) + z * (50 + z * ((-102) + z * ((-51) + z * (58 + z * (4 + z * ((-9) + z * 127))))))))))))))))))))))))))))))))))))))

theorem pow2_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_69 z * pow2_69 z = pow2_138_q z * f z + pow2_138 z + (139 : R) * pow2_138_mul_t z := by
  simp only [pow2_69, pow2_138_q, f, pow2_138, pow2_138_mul_t]
  
  ring

theorem pow2_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_69 z * pow2_69 z = pow2_138_q z * f z + pow2_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_138_mul_integer z


theorem pow2_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_69 z * pow2_69 z = pow2_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_138_mul z


theorem pow2_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 138 = pow2_138 z := by
  calc
    _ = u1 z ^ 69 * u1 z ^ 69 := by ring
    _ = pow2_69 z * pow2_69 z := by rw [pow2_69_pow z hz]
    _ = _ := pow2_138_root z hz


def pow2_139 {R : Type*} [CommRing R] (z : R) : R := (8 + z * (50 + z * (33 + z * (26 + z * (46 + z * (83 + z * (9 + z * (43 + z * (113 + z * (94 + z * (70 + z * (33 + z * (113 + z * (96 + z * (46 + z * (99 + z * (98 + z * (9 + z * (19 + z * 53)))))))))))))))))))

def pow2_139_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (2 + z * (107 + z * (104 + z * (26 + z * (46 + z * (89 + z * (65 + z * (119 + z * (100 + z * (36 + z * (53 + z * (81 + z * (91 + z * (50 + z * (102 + z * (50 + z * (113 + z * 121))))))))))))))))))

def pow2_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (85 + z * (111 + z * (0 + z * ((-2) + z * (120 + z * (81 + z * (29 + z * (185 + z * (140 + z * ((-28) + z * ((-43) + z * (33 + z * ((-147) + z * ((-45) + z * (118 + z * ((-18) + z * ((-159) + z * ((-85) + z * ((-265) + z * ((-201) + z * ((-143) + z * ((-317) + z * ((-150) + z * (15 + z * ((-74) + z * ((-200) + z * ((-115) + z * ((-317) + z * ((-227) + z * ((-98) + z * ((-85) + z * ((-201) + z * ((-14) + z * ((-108) + z * ((-60) + z * ((-35) + z * ((-97) + z * ((-38) + z * 64))))))))))))))))))))))))))))))))))))))

theorem pow2_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_138 z * u1 z = pow2_139_q z * f z + pow2_139 z + (139 : R) * pow2_139_mul_t z := by
  simp only [pow2_138, u1, pow2_139_q, f, pow2_139, pow2_139_mul_t]
  simp only [pow1_139]
  ring

theorem pow2_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow2_138 z * u1 z = pow2_139_q z * f z + pow2_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow2_139_mul_integer z


theorem pow2_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow2_138 z * u1 z = pow2_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_139_mul z


theorem pow2_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u1 z ^ 139 = pow2_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow2_138_pow z hz]
  exact pow2_139_root z hz


abbrev u2 {R : Type*} [CommRing R] (z : R) : R := pow2_139 z

theorem iterate2 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 2) = u2 z := by
  calc
    _ = (z ^ (139 ^ 1)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u1 z ^ 139 := congrArg (fun x : R => x ^ 139) (iterate1 z hz)
    _ = _ := pow2_139_pow z hz

end DimensionTen.Mod139

end

end OAI
