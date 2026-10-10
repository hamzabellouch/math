import OAI.Analysis.Quantum.DimensionTen.Mod41Powers10

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
abbrev g4 {R : Type*} [CommRing R] (z : R) : R := pow1_20_q z

def a4 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (32 + z * (23 + z * (37 + z * (23 + z * (13 + z * (30 + z * (0 + z * (17 + z * (6 + z * (8 + z * (18 + z * (15 + z * (11 + z * (34 + z * (11 + z * (0 + z * (1 + z * 32))))))))))))))))))

def b4 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (15 + z * (39 + z * (38 + z * (23 + z * (31 + z * (1 + z * (28 + z * (22 + z * (36 + z * (22 + z * (38 + z * (20 + z * (24 + z * (11 + z * (9 + z * (9 + z * (25 + z * (4 + z * 6)))))))))))))))))))

def bezout4_t {R : Type*} [CommRing R] (z : R) : R := (43 + z * (53 + z * (76 + z * (102 + z * (125 + z * (154 + z * (169 + z * (194 + z * (250 + z * (201 + z * (264 + z * (275 + z * (281 + z * (323 + z * (359 + z * (394 + z * (405 + z * (419 + z * (466 + z * (452 + z * (416 + z * (383 + z * (389 + z * (306 + z * (263 + z * (290 + z * (243 + z * (230 + z * (220 + z * (206 + z * (171 + z * (127 + z * (110 + z * (103 + z * (76 + z * (53 + z * (36 + z * (31 + z * 4))))))))))))))))))))))))))))))))))))))

theorem bezout4_integer {R : Type*} [CommRing R] (z : R) :
    a4 z * f z + b4 z * (u4 z - z) = g4 z + (41 : R) * bezout4_t z := by
  simp only [a4, b4, f, u4, g4, bezout4_t]
  simp only [pow4_41, pow1_20_q]
  ring

theorem bezout4 {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    a4 z * f z + b4 z * (u4 z - z) = g4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using bezout4_integer z


abbrev g10 {R : Type*} [CommRing R] (z : R) : R := pow1_20_q z

def a10 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (34 + z * (21 + z * (14 + z * (25 + z * (8 + z * (3 + z * (0 + z * (6 + z * (24 + z * (2 + z * (20 + z * (8 + z * (21 + z * (6 + z * (7 + z * (7 + z * (17 + z * 25))))))))))))))))))

def b10 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (12 + z * (14 + z * (36 + z * (37 + z * (27 + z * (33 + z * (1 + z * (34 + z * (22 + z * (1 + z * (20 + z * (31 + z * (28 + z * (26 + z * (30 + z * (33 + z * (11 + z * (37 + z * 36)))))))))))))))))))

def bezout10_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (50 + z * (72 + z * (83 + z * (114 + z * (114 + z * (109 + z * (110 + z * (179 + z * (170 + z * (150 + z * (224 + z * (196 + z * (246 + z * (196 + z * (250 + z * (275 + z * (281 + z * (306 + z * (307 + z * (281 + z * (245 + z * (231 + z * (218 + z * (185 + z * (189 + z * (179 + z * (160 + z * (153 + z * (129 + z * (109 + z * (95 + z * (114 + z * (87 + z * (56 + z * (43 + z * (43 + z * (32 + z * 5))))))))))))))))))))))))))))))))))))))

theorem bezout10_integer {R : Type*} [CommRing R] (z : R) :
    a10 z * f z + b10 z * (u10 z - z) = g10 z + (41 : R) * bezout10_t z := by
  simp only [a10, b10, f, u10, g10, bezout10_t]
  simp only [pow10_41, pow1_20_q]
  ring

theorem bezout10 {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    a10 z * f z + b10 z * (u10 z - z) = g10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using bezout10_integer z

end DimensionTen.Mod41

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod41
instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩


lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by simp only [f, map_add, map_mul, map_ofNat, map_one]

lemma map_u4 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (u4 z) = u4 (φ z) := by simp only [u4, pow4_41, map_add, map_mul, map_ofNat]
lemma map_u10 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (u10 z) = u10 (φ z) := by simp only [u10, pow10_41, map_add, map_mul, map_ofNat, map_one, map_zero]

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

section Field
variable (k : Type*) [Field k] [CharP k 41]

local instance nontrivial_root : Nontrivial (AdjoinRoot (f (X : k[X]))) :=
  AdjoinRoot.nontrivial _ (by
    rw [degree_eq_natDegree degree_f.monic.ne_zero, degree_f.natDegree_eq]
    norm_num)

local instance charP_root : CharP (AdjoinRoot (f (X : k[X]))) 41 :=
  charP_of_injective_algebraMap (algebraMap k _).injective 41

omit [CharP k 41] in
lemma root_f : f (AdjoinRoot.root (f (X : k[X]))) = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_f]
  exact AdjoinRoot.mk_self

lemma divides_twenty : f (X : k[X]) ∣ X ^ 41 ^ 20 - X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  rw [iterate20 _ (root_f k)]
  simp only [u20, u0, mul_one, zero_add, sub_self]

lemma divides_four : f (X : k[X]) ∣ X ^ 41 ^ 4 - u4 X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, map_u4, AdjoinRoot.mk_X]
  rw [iterate4 _ (root_f k), sub_self]

lemma divides_ten : f (X : k[X]) ∣ X ^ 41 ^ 10 - u10 X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, map_u10, AdjoinRoot.mk_X]
  rw [iterate10 _ (root_f k), sub_self]

lemma coprime_of_equiv {R : Type*} [CommRing R] {f g r : R}
    (hfr : IsCoprime f r) (hdiv : f ∣ g-r) : IsCoprime f g := by
  obtain ⟨q,hq⟩ := hdiv
  have hg : g = r + f*q := by rw [← hq]; ring
  rw [hg]
  exact hfr.add_mul_left_right q

lemma coprime_remainder_four {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    IsCoprime (f z) (u4 z-z) := ⟨a4 z, b4 z, bezout4 z⟩

lemma coprime_remainder_ten {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    IsCoprime (f z) (u10 z-z) := ⟨a10 z, b10 z, bezout10 z⟩

lemma coprime_of_equiv_sub {R : Type*} [CommRing R] (f a b c : R)
    (hr : IsCoprime f (b-c)) (hd : f ∣ a-b) : IsCoprime f (a-c) :=
  coprime_of_equiv hr (by simpa only [sub_sub_sub_cancel_right] using hd)

lemma coprime_of_equiv_sub_poly {k : Type*} [Field k] (f a b c : k[X])
    (hr : IsCoprime f (b-c)) (hd : f ∣ a-b) : IsCoprime f (a-c) :=
  coprime_of_equiv_sub f a b c hr hd

lemma coprime_four : IsCoprime (f (X : k[X])) (X ^ 41 ^ 4 - X) :=
  coprime_of_equiv_sub_poly (f (X : k[X])) (X ^ 41 ^ 4) (u4 X) X
    (coprime_remainder_four (X : k[X])) (divides_four k)

lemma coprime_ten : IsCoprime (f (X : k[X])) (X ^ 41 ^ 10 - X) :=
  coprime_of_equiv_sub_poly (f (X : k[X])) (X ^ 41 ^ 10) (u10 X) X
    (coprime_remainder_ten (X : k[X])) (divides_ten k)



theorem irreducible_degree_twenty {k : Type*} [Field k] [Finite k]
    (f : k[X]) (hd : f.natDegree = 20)
    (h20 : f ∣ X ^ (Nat.card k) ^ 20 - X)
    (h4 : IsCoprime f (X ^ (Nat.card k) ^ 4 - X))
    (h10 : IsCoprime f (X ^ (Nat.card k) ^ 10 - X)) : Irreducible f := by
  have hf : f ≠ 0 := by intro h; simp [h] at hd
  obtain ⟨g, hig, hgf⟩ := exists_irreducible_of_natDegree_pos (f := f) (by omega)
  have hdiv := hig.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (dvd_trans hgf h20)
  have hle : g.natDegree ≤ 20 := hd ▸ natDegree_le_of_dvd hgf hf
  have hgd : g.natDegree = 20 := by
    by_contra hne
    have hc : ∀ d : Fin 21, d.val ∣ 20 → d.val ≠ 20 → d.val ∣ 4 ∨ d.val ∣ 10 := by
      decide
    rcases hc ⟨g.natDegree, by omega⟩ hdiv hne with h | h
    · exact hig.not_isUnit (h4.isUnit_of_dvd' hgf
        (hig.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp h))
    · exact hig.not_isUnit (h10.isUnit_of_dvd' hgf
        (hig.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp h))
  exact (associated_of_dvd_of_natDegree_le hgf hf (by omega)).irreducible_iff.mp hig


theorem irreducible_f_of_card [Finite k] (hc : Nat.card k = 41) :
    Irreducible (f (X : k[X])) := by
  apply irreducible_degree_twenty _ degree_f.natDegree_eq
  · simpa only [hc] using divides_twenty k
  · simpa only [hc] using coprime_four k
  · simpa only [hc] using coprime_ten k

end Field

theorem irreducible_f : Irreducible (f (X : (ZMod 41)[X])) :=
  irreducible_f_of_card (ZMod 41) (by simp)

end DimensionTen.Mod41

end
end

end

end OAI
