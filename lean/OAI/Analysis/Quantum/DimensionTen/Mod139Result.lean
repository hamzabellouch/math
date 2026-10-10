import OAI.Analysis.Quantum.DimensionTen.Mod139Powers10

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def g1 {R : Type*} [CommRing R] (z : R) : R := (18 + z * 1)

def a1 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (58 + z * (93 + z * (71 + z * (14 + z * (127 + z * (39 + z * (101 + z * (100 + z * (125 + z * (16 + z * (96 + z * (40 + z * (75 + z * (120 + z * (31 + z * (5 + z * 106)))))))))))))))))

def b1 {R : Type*} [CommRing R] (z : R) : R := (45 + z * (129 + z * (121 + z * (47 + z * (93 + z * (123 + z * (131 + z * (0 + z * (97 + z * (133 + z * (104 + z * (137 + z * (136 + z * (105 + z * (66 + z * (113 + z * (29 + z * (130 + z * 32))))))))))))))))))

def bezout1_t {R : Type*} [CommRing R] (z : R) : R := (93 + z * (264 + z * (441 + z * (515 + z * (583 + z * (749 + z * (815 + z * (763 + z * (912 + z * (1182 + z * (1231 + z * (1305 + z * (1464 + z * (1514 + z * (1464 + z * (1619 + z * (1588 + z * (1667 + z * (1671 + z * (1636 + z * (1563 + z * (1587 + z * (1268 + z * (1285 + z * (1227 + z * (995 + z * (937 + z * (1009 + z * (831 + z * (651 + z * (714 + z * (435 + z * (512 + z * (386 + z * (257 + z * (202 + z * (233 + z * 30)))))))))))))))))))))))))))))))))))))

theorem bezout1_integer {R : Type*} [CommRing R] (z : R) :
    a1 z * f z + b1 z * (u1 z - z) = g1 z + (139 : R) * bezout1_t z := by
  simp only [a1, b1, f, u1, g1, bezout1_t]
  simp only [pow1_139]
  ring

theorem bezout1 {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    a1 z * f z + b1 z * (u1 z - z) = g1 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using bezout1_integer z


def div1_f {R : Type*} [CommRing R] (z : R) : R := (29 + z * (121 + z * (62 + z * (112 + z * (23 + z * (86 + z * (106 + z * (37 + z * (10 + z * (91 + z * (72 + z * (129 + z * (126 + z * (62 + z * (77 + z * (47 + z * (27 + z * (68 + z * (110 + z * 1)))))))))))))))))))

def factor1_f_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-15) + z * ((-8) + z * ((-14) + z * ((-3) + z * ((-11) + z * ((-14) + z * ((-5) + z * ((-1) + z * ((-11) + z * ((-9) + z * ((-17) + z * ((-17) + z * ((-8) + z * ((-10) + z * ((-6) + z * ((-3) + z * ((-9) + z * ((-14) + z * (0 + z * 0))))))))))))))))))))

theorem factor1_f_integer {R : Type*} [CommRing R] (z : R) :
    f z = g1 z * div1_f z + (139 : R) * factor1_f_t z := by
  simp only [f, g1, div1_f, factor1_f_t]
  
  ring

theorem factor1_f {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    f z = g1 z * div1_f z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using factor1_f_integer z


def div1_u1 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (116 + z * (99 + z * (22 + z * (67 + z * (92 + z * (58 + z * (47 + z * (103 + z * (21 + z * (49 + z * (105 + z * (42 + z * (100 + z * (80 + z * (138 + z * (70 + z * (10 + z * 127))))))))))))))))))

def factor1_u1_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-15) + z * ((-13) + z * ((-3) + z * ((-8) + z * ((-12) + z * ((-8) + z * ((-6) + z * ((-13) + z * ((-3) + z * ((-6) + z * ((-13) + z * ((-6) + z * ((-13) + z * ((-11) + z * ((-18) + z * ((-10) + z * ((-1) + z * ((-16) + z * 0)))))))))))))))))))

theorem factor1_u1_integer {R : Type*} [CommRing R] (z : R) :
    (u1 z - z) = g1 z * div1_u1 z + (139 : R) * factor1_u1_t z := by
  simp only [u1, g1, div1_u1, factor1_u1_t]
  simp only [pow1_139]
  ring

theorem factor1_u1 {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    (u1 z - z) = g1 z * div1_u1 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using factor1_u1_integer z


def df {R : Type*} [CommRing R] (z : R) : R := (122 + z * (111 + z * (118 + z * (19 + z * (71 + z * (10 + z * (122 + z * (68 + z * (98 + z * (109 + z * (63 + z * (130 + z * (22 + z * (117 + z * (84 + z * (49 + z * (0 + z * (29 + z * (69 + z * 20)))))))))))))))))))

def da {R : Type*} [CommRing R] (z : R) : R := (39 + z * (17 + z * (73 + z * (16 + z * (132 + z * (18 + z * (8 + z * (1 + z * (121 + z * (9 + z * (71 + z * (47 + z * (16 + z * (84 + z * (111 + z * (31 + z * (68 + z * (50 + z * 107))))))))))))))))))

def db {R : Type*} [CommRing R] (z : R) : R := (110 + z * (32 + z * (66 + z * (134 + z * (55 + z * (51 + z * (89 + z * (93 + z * (107 + z * (120 + z * (114 + z * (89 + z * (65 + z * (79 + z * (127 + z * (10 + z * (116 + z * (55 + z * (55 + z * 85)))))))))))))))))))

def separable_bezout_t {R : Type*} [CommRing R] (z : R) : R := (126 + z * (163 + z * (282 + z * (341 + z * (498 + z * (474 + z * (548 + z * (570 + z * (721 + z * (835 + z * (915 + z * (1075 + z * (1033 + z * (1137 + z * (1325 + z * (1241 + z * (1352 + z * (1485 + z * (1571 + z * (1372 + z * (1481 + z * (1296 + z * (1184 + z * (1208 + z * (1034 + z * (914 + z * (902 + z * (984 + z * (703 + z * (675 + z * (539 + z * (476 + z * (493 + z * (354 + z * (269 + z * (155 + z * (178 + z * (149 + z * 13))))))))))))))))))))))))))))))))))))))

theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (139 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod139

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod139

lemma horner_monic_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (a : R) :
    (C a + X * p).IsMonicOfDegree (n+1) := by
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · rw [natDegree_C_add, monic_X.natDegree_mul hp.monic, natDegree_X, hp.natDegree_eq]
    omega
  · simp only [coeff_add, coeff_C, Nat.add_one_ne_zero, ite_false, zero_add, coeff_X_mul]
    simpa only [hp.natDegree_eq] using hp.monic.coeff_natDegree

lemma horner_zero_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) : (0 + X * p).IsMonicOfDegree (n+1) := by
  simpa only [C_0] using horner_monic_degree hp 0

lemma degree_f {R : Type*} [CommRing R] [Nontrivial R] :
    (f (X : R[X])).IsMonicOfDegree 20 := by
  unfold f
  repeat' first | apply horner_monic_degree | apply horner_zero_degree
  exact ⟨natDegree_one, monic_one⟩

lemma degree_g {R : Type*} [CommRing R] [Nontrivial R] :
    (g1 (X : R[X])).IsMonicOfDegree 1 := by
  unfold g1
  repeat' first | apply horner_monic_degree | apply horner_zero_degree
  exact ⟨natDegree_one, monic_one⟩

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one, map_zero]

lemma map_g1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (g1 z) = g1 (φ z) := by
  simp only [g1, map_add, map_mul, map_ofNat, map_one]

def derivative_extra {R : Type*} [CommRing R] (z : R) : R := (0 + z * (1 + z * (2 + z * (3 + z * (1 + z * (2 + z * (3 + z * (4 + z * (7 + z * (9 + z * (2 + z * (2 + z * (12 + z * (5 + z * (9 + z * (13 + z * (0 + z * (13 + z * (17 + z * 0)))))))))))))))))))
lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (139 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one, derivative_zero]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 139] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (139 : k[X]) = 0 := CharP.cast_eq_zero _ 139
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

lemma fixed_iff_g_zero {k : Type*} [Field k] [CharP k 139] (z : k) (hz : f z = 0) :
    z ^ (139 ^ 1) = z ↔ g1 z = 0 := by
  rw [iterate1 z hz]
  constructor
  · intro h
    have hb := bezout1 z
    simpa only [hz, mul_zero, h, sub_self, zero_add] using hb.symm
  · intro h
    apply sub_eq_zero.mp
    rw [factor1_u1, h, zero_mul]

end DimensionTen.Mod139

end
end

end

end OAI
