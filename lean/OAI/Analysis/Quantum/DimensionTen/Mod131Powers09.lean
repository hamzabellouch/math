import OAI.Analysis.Quantum.DimensionTen.Mod131Powers08

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow17_2 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (53 + z * (19 + z * (102 + z * (43 + z * (109 + z * (104 + z * (86 + z * (104 + z * (44 + z * (60 + z * (113 + z * (32 + z * (124 + z * (53 + z * (7 + z * (11 + z * (117 + z * (33 + z * 61)))))))))))))))))))

def pow17_2_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (57 + z * (64 + z * (54 + z * (99 + z * (45 + z * (56 + z * (98 + z * (47 + z * (42 + z * (106 + z * (82 + z * (35 + z * (19 + z * (103 + z * (50 + z * (120 + z * (7 + z * 94))))))))))))))))))

def pow17_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-39) + z * ((-28) + z * ((-58) + z * ((-43) + z * ((-37) + z * ((-99) + z * (42 + z * ((-85) + z * ((-36) + z * ((-72) + z * ((-31) + z * ((-105) + z * ((-153) + z * (11 + z * ((-84) + z * ((-92) + z * ((-30) + z * (42 + z * ((-5) + z * ((-166) + z * (49 + z * ((-50) + z * (17 + z * ((-89) + z * (60 + z * (10 + z * ((-129) + z * ((-66) + z * (67 + z * (31 + z * (43 + z * ((-27) + z * (2 + z * ((-23) + z * ((-3) + z * ((-37) + z * ((-14) + z * ((-41) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow17_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z + (131 : R) * pow17_2_mul_t z := by
  simp only [u16, pow17_2_q, f, pow17_2, pow17_2_mul_t]
  simp only [pow16_131]
  ring

theorem pow17_2_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_2_mul_integer z


theorem pow17_2_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z * u16 z = pow17_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_2_mul z


theorem pow17_2_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 2 = pow17_2 z := by
  calc
    _ = u16 z ^ 1 * u16 z ^ 1 := by ring
    _ = u16 z * u16 z := by simp only [pow_one]
    _ = _ := pow17_2_root z hz


def pow17_4 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (13 + z * (110 + z * (93 + z * (0 + z * (111 + z * (55 + z * (19 + z * (50 + z * (29 + z * (18 + z * (102 + z * (70 + z * (90 + z * (117 + z * (56 + z * (21 + z * (54 + z * (125 + z * 119)))))))))))))))))))

def pow17_4_q {R : Type*} [CommRing R] (z : R) : R := (90 + z * (30 + z * (44 + z * (100 + z * (1 + z * (115 + z * (19 + z * (22 + z * (16 + z * (67 + z * (48 + z * (19 + z * (110 + z * (77 + z * (113 + z * (114 + z * (51 + z * (4 + z * 53))))))))))))))))))

def pow17_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-5) + z * ((-37) + z * (5 + z * (5 + z * ((-52) + z * (138 + z * (33 + z * (143 + z * (181 + z * (127 + z * (266 + z * (188 + z * (221 + z * (232 + z * (153 + z * (170 + z * (159 + z * (201 + z * (193 + z * (177 + z * (97 + z * (205 + z * (73 + z * (239 + z * (125 + z * (22 + z * (37 + z * (40 + z * ((-46) + z * (118 + z * ((-65) + z * ((-15) + z * ((-73) + z * ((-1) + z * (21 + z * (91 + z * (4 + z * 28))))))))))))))))))))))))))))))))))))))

theorem pow17_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z + (131 : R) * pow17_4_mul_t z := by
  simp only [pow17_2, pow17_4_q, f, pow17_4, pow17_4_mul_t]
  
  ring

theorem pow17_4_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_4_mul_integer z


theorem pow17_4_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_2 z * pow17_2 z = pow17_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_4_mul z


theorem pow17_4_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 4 = pow17_4 z := by
  calc
    _ = u16 z ^ 2 * u16 z ^ 2 := by ring
    _ = pow17_2 z * pow17_2 z := by rw [pow17_2_pow z hz]
    _ = _ := pow17_4_root z hz


def pow17_8 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (28 + z * (71 + z * (90 + z * (100 + z * (48 + z * (52 + z * (26 + z * (90 + z * (23 + z * (5 + z * (54 + z * (59 + z * (128 + z * (57 + z * (79 + z * (44 + z * (130 + z * (97 + z * 44)))))))))))))))))))

def pow17_8_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (99 + z * (35 + z * (121 + z * (81 + z * (79 + z * (103 + z * (33 + z * (127 + z * (120 + z * (67 + z * (43 + z * (74 + z * (72 + z * (79 + z * (38 + z * (33 + z * (72 + z * 13))))))))))))))))))

def pow17_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * ((-34) + z * (1 + z * ((-43) + z * ((-2) + z * (25 + z * ((-120) + z * (3 + z * ((-55) + z * ((-204) + z * ((-176) + z * ((-134) + z * ((-267) + z * ((-173) + z * ((-141) + z * ((-129) + z * ((-11) + z * ((-113) + z * ((-99) + z * ((-32) + z * (38 + z * (20 + z * ((-31) + z * (78 + z * (126 + z * (25 + z * (83 + z * (103 + z * (85 + z * (183 + z * (257 + z * (268 + z * (307 + z * (216 + z * (94 + z * (87 + z * (175 + z * (220 + z * 108))))))))))))))))))))))))))))))))))))))

theorem pow17_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z + (131 : R) * pow17_8_mul_t z := by
  simp only [pow17_4, pow17_8_q, f, pow17_8, pow17_8_mul_t]
  
  ring

theorem pow17_8_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_4 z * pow17_4 z = pow17_8_q z * f z + pow17_8 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_8_mul_integer z


theorem pow17_8_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_4 z * pow17_4 z = pow17_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_8_mul z


theorem pow17_8_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 8 = pow17_8 z := by
  calc
    _ = u16 z ^ 4 * u16 z ^ 4 := by ring
    _ = pow17_4 z * pow17_4 z := by rw [pow17_4_pow z hz]
    _ = _ := pow17_8_root z hz


def pow17_16 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (13 + z * (58 + z * (85 + z * (110 + z * (130 + z * (55 + z * (56 + z * (9 + z * (74 + z * (83 + z * (114 + z * (48 + z * (103 + z * (32 + z * (92 + z * (32 + z * (52 + z * (104 + z * 60)))))))))))))))))))

def pow17_16_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (59 + z * (38 + z * (46 + z * (39 + z * (97 + z * (8 + z * (91 + z * (28 + z * (102 + z * (110 + z * (130 + z * (88 + z * (105 + z * (32 + z * (101 + z * (43 + z * (101 + z * 102))))))))))))))))))

def pow17_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-24) + z * ((-29) + z * ((-24) + z * (19 + z * (22 + z * (58 + z * (57 + z * (52 + z * ((-39) + z * ((-37) + z * ((-58) + z * ((-169) + z * ((-191) + z * ((-166) + z * ((-87) + z * ((-48) + z * ((-44) + z * ((-153) + z * (46 + z * ((-26) + z * (130 + z * ((-113) + z * ((-138) + z * ((-115) + z * ((-36) + z * ((-66) + z * ((-72) + z * ((-80) + z * ((-57) + z * (141 + z * (147 + z * (174 + z * (69 + z * (72 + z * (116 + z * (62 + z * (13 + z * 14))))))))))))))))))))))))))))))))))))))

theorem pow17_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z + (131 : R) * pow17_16_mul_t z := by
  simp only [pow17_8, pow17_16_q, f, pow17_16, pow17_16_mul_t]
  
  ring

theorem pow17_16_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_8 z * pow17_8 z = pow17_16_q z * f z + pow17_16 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_16_mul_integer z


theorem pow17_16_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_8 z * pow17_8 z = pow17_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_16_mul z


theorem pow17_16_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 16 = pow17_16 z := by
  calc
    _ = u16 z ^ 8 * u16 z ^ 8 := by ring
    _ = pow17_8 z * pow17_8 z := by rw [pow17_8_pow z hz]
    _ = _ := pow17_16_root z hz


def pow17_32 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (25 + z * (26 + z * (42 + z * (111 + z * (3 + z * (52 + z * (49 + z * (7 + z * (52 + z * (69 + z * (13 + z * (101 + z * (105 + z * (124 + z * (86 + z * (24 + z * (1 + z * (36 + z * 5)))))))))))))))))))

def pow17_32_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (69 + z * (22 + z * (98 + z * (70 + z * (76 + z * (85 + z * (16 + z * (64 + z * (10 + z * (89 + z * (24 + z * (53 + z * (49 + z * (46 + z * (27 + z * (8 + z * (69 + z * 63))))))))))))))))))

def pow17_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-31) + z * ((-32) + z * ((-58) + z * ((-36) + z * ((-42) + z * (3 + z * (108 + z * (63 + z * (127 + z * (44 + z * (27 + z * (14 + z * (76 + z * (153 + z * (210 + z * (256 + z * (146 + z * (210 + z * (121 + z * (338 + z * (234 + z * (313 + z * (289 + z * (311 + z * (126 + z * (160 + z * (175 + z * (270 + z * (163 + z * (168 + z * (151 + z * (142 + z * (99 + z * (71 + z * (53 + z * (67 + z * (63 + z * 27))))))))))))))))))))))))))))))))))))))

theorem pow17_32_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_16 z * pow17_16 z = pow17_32_q z * f z + pow17_32 z + (131 : R) * pow17_32_mul_t z := by
  simp only [pow17_16, pow17_32_q, f, pow17_32, pow17_32_mul_t]
  
  ring

theorem pow17_32_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_16 z * pow17_16 z = pow17_32_q z * f z + pow17_32 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_32_mul_integer z


theorem pow17_32_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_16 z * pow17_16 z = pow17_32 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_32_mul z


theorem pow17_32_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 32 = pow17_32 z := by
  calc
    _ = u16 z ^ 16 * u16 z ^ 16 := by ring
    _ = pow17_16 z * pow17_16 z := by rw [pow17_16_pow z hz]
    _ = _ := pow17_32_root z hz


def pow17_64 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (53 + z * (57 + z * (30 + z * (79 + z * (57 + z * (109 + z * (91 + z * (65 + z * (18 + z * (88 + z * (88 + z * (106 + z * (9 + z * (87 + z * (80 + z * (66 + z * (53 + z * (47 + z * 41)))))))))))))))))))

def pow17_64_q {R : Type*} [CommRing R] (z : R) : R := (72 + z * (119 + z * (5 + z * (3 + z * (64 + z * (38 + z * (102 + z * (1 + z * (25 + z * (98 + z * (37 + z * (95 + z * (122 + z * (34 + z * (116 + z * (27 + z * (83 + z * (20 + z * 25))))))))))))))))))

def pow17_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (77 + z * ((-27) + z * ((-29) + z * (11 + z * (131 + z * ((-103) + z * ((-41) + z * (66 + z * ((-75) + z * ((-111) + z * (50 + z * ((-150) + z * ((-75) + z * ((-16) + z * (32 + z * (54 + z * ((-39) + z * ((-187) + z * (9 + z * ((-107) + z * ((-171) + z * ((-138) + z * ((-92) + z * ((-164) + z * ((-48) + z * ((-77) + z * (62 + z * (25 + z * (46 + z * ((-33) + z * ((-72) + z * ((-79) + z * ((-60) + z * ((-65) + z * ((-56) + z * ((-58) + z * ((-12) + z * ((-10) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow17_64_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_32 z * pow17_32 z = pow17_64_q z * f z + pow17_64 z + (131 : R) * pow17_64_mul_t z := by
  simp only [pow17_32, pow17_64_q, f, pow17_64, pow17_64_mul_t]
  
  ring

theorem pow17_64_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_32 z * pow17_32 z = pow17_64_q z * f z + pow17_64 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_64_mul_integer z


theorem pow17_64_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_32 z * pow17_32 z = pow17_64 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_64_mul z


theorem pow17_64_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 64 = pow17_64 z := by
  calc
    _ = u16 z ^ 32 * u16 z ^ 32 := by ring
    _ = pow17_32 z * pow17_32 z := by rw [pow17_32_pow z hz]
    _ = _ := pow17_64_root z hz


def pow17_65 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (18 + z * (22 + z * (51 + z * (75 + z * (34 + z * (43 + z * (71 + z * (71 + z * (89 + z * (48 + z * (104 + z * (79 + z * (114 + z * (38 + z * (100 + z * (42 + z * (42 + z * (25 + z * 86)))))))))))))))))))

def pow17_65_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (29 + z * (2 + z * (0 + z * (44 + z * (114 + z * (86 + z * (16 + z * (105 + z * (91 + z * (10 + z * (72 + z * (57 + z * (17 + z * (25 + z * (39 + z * (13 + z * (39 + z * 91))))))))))))))))))

def pow17_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-1) + z * (28 + z * (27 + z * (46 + z * (37 + z * (34 + z * (116 + z * (57 + z * (53 + z * (17 + z * (129 + z * (98 + z * (10 + z * (112 + z * (231 + z * (60 + z * (121 + z * (231 + z * (215 + z * (134 + z * (150 + z * (163 + z * (153 + z * (126 + z * (67 + z * (70 + z * (129 + z * (123 + z * (122 + z * (45 + z * (100 + z * (119 + z * (52 + z * (9 + z * (19 + z * ((-8) + z * ((-32) + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow17_65_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_64 z * u16 z = pow17_65_q z * f z + pow17_65 z + (131 : R) * pow17_65_mul_t z := by
  simp only [pow17_64, u16, pow17_65_q, f, pow17_65, pow17_65_mul_t]
  simp only [pow16_131]
  ring

theorem pow17_65_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_64 z * u16 z = pow17_65_q z * f z + pow17_65 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_65_mul_integer z


theorem pow17_65_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_64 z * u16 z = pow17_65 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_65_mul z


theorem pow17_65_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 65 = pow17_65 z := by
  rw [show 65 = 64 + 1 by rfl, pow_succ, pow17_64_pow z hz]
  exact pow17_65_root z hz


def pow17_130 {R : Type*} [CommRing R] (z : R) : R := (60 + z * (90 + z * (29 + z * (14 + z * (34 + z * (125 + z * (5 + z * (4 + z * (79 + z * (86 + z * (4 + z * (86 + z * (39 + z * (124 + z * (14 + z * (7 + z * (1 + z * (57 + z * (55 + z * 84)))))))))))))))))))

def pow17_130_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (94 + z * (34 + z * (6 + z * (71 + z * (23 + z * (79 + z * (21 + z * (104 + z * (28 + z * (119 + z * (104 + z * (122 + z * (23 + z * (124 + z * (40 + z * (78 + z * (78 + z * 60))))))))))))))))))

def pow17_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * ((-13) + z * ((-17) + z * (35 + z * (79 + z * ((-18) + z * ((-41) + z * (104 + z * (29 + z * (32 + z * (5 + z * (106 + z * ((-5) + z * (62 + z * ((-3) + z * (115 + z * (21 + z * ((-18) + z * (14 + z * (38 + z * (45 + z * ((-7) + z * (54 + z * (8 + z * (111 + z * ((-14) + z * (112 + z * ((-5) + z * (86 + z * ((-70) + z * (42 + z * (29 + z * (82 + z * ((-63) + z * (36 + z * ((-26) + z * ((-7) + z * (2 + z * 56))))))))))))))))))))))))))))))))))))))

theorem pow17_130_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_65 z * pow17_65 z = pow17_130_q z * f z + pow17_130 z + (131 : R) * pow17_130_mul_t z := by
  simp only [pow17_65, pow17_130_q, f, pow17_130, pow17_130_mul_t]
  
  ring

theorem pow17_130_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_65 z * pow17_65 z = pow17_130_q z * f z + pow17_130 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_130_mul_integer z


theorem pow17_130_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_65 z * pow17_65 z = pow17_130 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_130_mul z


theorem pow17_130_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 130 = pow17_130 z := by
  calc
    _ = u16 z ^ 65 * u16 z ^ 65 := by ring
    _ = pow17_65 z * pow17_65 z := by rw [pow17_65_pow z hz]
    _ = _ := pow17_130_root z hz


def pow17_131 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (130 + z * (125 + z * (16 + z * (93 + z * (10 + z * (91 + z * (22 + z * (124 + z * (28 + z * (123 + z * (45 + z * (123 + z * (79 + z * (93 + z * (97 + z * (110 + z * (80 + z * (89 + z * 105)))))))))))))))))))

def pow17_131_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (45 + z * (35 + z * (22 + z * (101 + z * (24 + z * (18 + z * (17 + z * (13 + z * (26 + z * (29 + z * (102 + z * (129 + z * (4 + z * (51 + z * (24 + z * (79 + z * (58 + z * 81))))))))))))))))))

def pow17_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * (2 + z * ((-19) + z * (3 + z * ((-26) + z * ((-15) + z * (71 + z * ((-21) + z * (9 + z * (1 + z * (103 + z * ((-46) + z * ((-3) + z * (59 + z * (107 + z * ((-25) + z * (2 + z * (37 + z * (102 + z * ((-84) + z * ((-28) + z * (51 + z * (34 + z * ((-81) + z * (70 + z * (55 + z * (72 + z * ((-87) + z * ((-52) + z * ((-55) + z * (24 + z * ((-10) + z * (7 + z * ((-56) + z * ((-9) + z * ((-1) + z * (27 + z * ((-17) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow17_131_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_130 z * u16 z = pow17_131_q z * f z + pow17_131 z + (131 : R) * pow17_131_mul_t z := by
  simp only [pow17_130, u16, pow17_131_q, f, pow17_131, pow17_131_mul_t]
  simp only [pow16_131]
  ring

theorem pow17_131_mul {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    pow17_130 z * u16 z = pow17_131_q z * f z + pow17_131 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using pow17_131_mul_integer z


theorem pow17_131_root {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : pow17_130 z * u16 z = pow17_131 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_131_mul z


theorem pow17_131_pow {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : u16 z ^ 131 = pow17_131 z := by
  rw [show 131 = 130 + 1 by rfl, pow_succ, pow17_130_pow z hz]
  exact pow17_131_root z hz


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_131 z

theorem iterate17 {R : Type*} [CommRing R] [CharP R 131]
    (z : R) (hz : f z = 0) : z ^ (131 ^ 17) = u17 z := by
  calc
    _ = (z ^ (131 ^ 16)) ^ 131 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 131 := congrArg (fun x : R => x ^ 131) (iterate16 z hz)
    _ = _ := pow17_131_pow z hz

end DimensionTen.Mod131

end

end OAI
