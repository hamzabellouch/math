import OAI.Analysis.Quantum.DimensionTen.Mod131Powers09

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def g17 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (104 + z * (95 + z * (82 + z * (11 + z * (75 + z * (106 + z * (48 + z * (52 + z * (8 + z * (79 + z * (49 + z * (111 + z * (2 + z * (54 + z * (63 + z * (80 + z * (41 + z * 1))))))))))))))))))

def a17 {R : Type*} [CommRing R] (_ : R) : R := 106

def b17 {R : Type*} [CommRing R] (z : R) : R := (47 + z * 125)

def bezout17_t {R : Type*} [CommRing R] (z : R) : R := (60 + z * (136 + z * (219 + z * (143 + z * (106 + z * (184 + z * (43 + z * (151 + z * (146 + z * (172 + z * (84 + z * (227 + z * (155 + z * (208 + z * (114 + z * (153 + z * (201 + z * (173 + z * (156 + z * (176 + z * 101))))))))))))))))))))

theorem bezout17_integer {R : Type*} [CommRing R] (z : R) :
    a17 z * f z + b17 z * (u17 z - z) = g17 z + (131 : R) * bezout17_t z := by
  simp only [a17, b17, f, u17, g17, bezout17_t]
  simp only [pow17_131]
  ring

theorem bezout17 {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    a17 z * f z + b17 z * (u17 z - z) = g17 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using bezout17_integer z


def div17_f {R : Type*} [CommRing R] (z : R) : R := (2 + z * (25 + z * 1))

def factor17_f_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-6) + z * ((-21) + z * ((-20) + z * ((-16) + z * ((-3) + z * ((-16) + z * ((-21) + z * ((-10) + z * ((-10) + z * ((-3) + z * ((-15) + z * ((-11) + z * ((-21) + z * ((-2) + z * ((-11) + z * ((-13) + z * ((-16) + z * ((-8) + z * (0 + z * 0))))))))))))))))))))

theorem factor17_f_integer {R : Type*} [CommRing R] (z : R) :
    f z = g17 z * div17_f z + (131 : R) * factor17_f_t z := by
  simp only [f, g17, div17_f, factor17_f_t]
  
  ring

theorem factor17_f {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    f z = g17 z * div17_f z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using factor17_f_integer z


def div17_u17 {R : Type*} [CommRing R] (z : R) : R := (107 + z * 105)

def factor17_u17_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-104) + z * ((-160) + z * ((-143) + z * ((-74) + z * ((-70) + z * ((-146) + z * ((-124) + z * ((-80) + z * ((-48) + z * ((-70) + z * ((-103) + z * ((-129) + z * ((-90) + z * ((-45) + z * ((-94) + z * ((-115) + z * ((-97) + z * ((-33) + z * 0)))))))))))))))))))

theorem factor17_u17_integer {R : Type*} [CommRing R] (z : R) :
    (u17 z - z) = g17 z * div17_u17 z + (131 : R) * factor17_u17_t z := by
  simp only [u17, g17, div17_u17, factor17_u17_t]
  simp only [pow17_131]
  ring

theorem factor17_u17 {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    (u17 z - z) = g17 z * div17_u17 z := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using factor17_u17_integer z


def df {R : Type*} [CommRing R] (z : R) : R := (47 + z * (128 + z * (69 + z * (22 + z * (46 + z * (12 + z * (97 + z * (14 + z * (93 + z * (39 + z * (97 + z * (103 + z * (84 + z * (98 + z * (31 + z * (66 + z * (47 + z * (14 + z * (75 + z * 20)))))))))))))))))))

def da {R : Type*} [CommRing R] (z : R) : R := (87 + z * (35 + z * (111 + z * (110 + z * (33 + z * (84 + z * (107 + z * (66 + z * (16 + z * (96 + z * (53 + z * (63 + z * (25 + z * (84 + z * (129 + z * (21 + z * (82 + z * (94 + z * 23))))))))))))))))))

def db {R : Type*} [CommRing R] (z : R) : R := (97 + z * (91 + z * (127 + z * (46 + z * (9 + z * (0 + z * (82 + z * (112 + z * (45 + z * (17 + z * (60 + z * (42 + z * (103 + z * (71 + z * (9 + z * (129 + z * (93 + z * (119 + z * (76 + z * 84)))))))))))))))))))

def separable_bezout_t {R : Type*} [CommRing R] (z : R) : R := (68 + z * (172 + z * (283 + z * (319 + z * (324 + z * (307 + z * (365 + z * (541 + z * (646 + z * (556 + z * (685 + z * (804 + z * (807 + z * (997 + z * (1041 + z * (941 + z * (1063 + z * (1117 + z * (1343 + z * (1219 + z * (1055 + z * (1126 + z * (1013 + z * (899 + z * (861 + z * (1011 + z * (789 + z * (748 + z * (742 + z * (660 + z * (607 + z * (444 + z * (394 + z * (360 + z * (254 + z * (213 + z * (129 + z * (72 + z * 13))))))))))))))))))))))))))))))))))))))

theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (131 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 131] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (131 : R) = 0 := CharP.cast_eq_zero R 131
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod131

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod131

lemma horner_monic_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (a : R) :
    (C a + X * p).IsMonicOfDegree (n+1) := by
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · rw [natDegree_C_add, monic_X.natDegree_mul hp.monic, natDegree_X, hp.natDegree_eq]
    omega
  · simp only [coeff_add, coeff_C, Nat.add_one_ne_zero, ite_false, zero_add, coeff_X_mul]
    simpa only [hp.natDegree_eq] using hp.monic.coeff_natDegree

lemma degree_f {R : Type*} [CommRing R] [Nontrivial R] :
    (f (X : R[X])).IsMonicOfDegree 20 := by
  unfold f
  repeat' apply horner_monic_degree
  exact ⟨natDegree_one, monic_one⟩

lemma degree_g {R : Type*} [CommRing R] [Nontrivial R] :
    (g17 (X : R[X])).IsMonicOfDegree 18 := by
  unfold g17
  repeat' apply horner_monic_degree
  exact ⟨natDegree_one, monic_one⟩

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one]

lemma map_g17 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (g17 z) = g17 (φ z) := by
  simp only [g17, map_add, map_mul, map_ofNat, map_one]

def derivative_extra {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (2 + z * (4 + z * (0 + z * (3 + z * (6 + z * (3 + z * (1 + z * (9 + z * (7 + z * (7 + z * (0 + z * (4 + z * (10 + z * (6 + z * (8 + z * (9 + z * 0)))))))))))))))))))
lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (131 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 131] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (131 : k[X]) = 0 := CharP.cast_eq_zero _ 131
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

lemma fixed_iff_g_zero {k : Type*} [Field k] [CharP k 131] (z : k) (hz : f z = 0) :
    z ^ (131 ^ 17) = z ↔ g17 z = 0 := by
  rw [iterate17 z hz]
  constructor
  · intro h
    have hb := bezout17 z
    simpa only [hz, mul_zero, h, sub_self, zero_add] using hb.symm
  · intro h
    apply sub_eq_zero.mp
    rw [factor17_u17, h, zero_mul]

end DimensionTen.Mod131

end
end

end

end OAI
