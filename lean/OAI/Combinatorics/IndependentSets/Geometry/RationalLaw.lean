import Mathlib

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

structure RationalLaw (O : Type*) [Fintype O] where
  weight : O → ℚ
  nonneg : ∀ o, 0 ≤ weight o
  total : ∑ o, weight o = 1

namespace RationalLaw
variable {O : Type*} [Fintype O]

def denominator (p : RationalLaw O) : ℕ := ∏ o, (p.weight o).den

def copies (p : RationalLaw O) (o : O) : ℕ :=
  (p.denominator / (p.weight o).den) * (p.weight o).num.toNat

lemma denominator_pos (p : RationalLaw O) : 0 < p.denominator := by
  apply Finset.prod_pos
  intro o _; exact Rat.den_pos _

lemma denominator_dvd (p : RationalLaw O) (o : O) :
    (p.weight o).den ∣ p.denominator := Finset.dvd_prod_of_mem _ (Finset.mem_univ o)

lemma copies_eq (p : RationalLaw O) (o : O) :
    (p.copies o : ℚ) = p.denominator * p.weight o := by
  have hnum : 0 ≤ (p.weight o).num := Rat.num_nonneg.mpr (p.nonneg o)
  have hden : ((p.weight o).den : ℚ) ≠ 0 := by
    exact_mod_cast (Rat.den_pos (p.weight o)).ne'
  have hdiv : (p.denominator / (p.weight o).den : ℕ) * (p.weight o).den = p.denominator :=
    Nat.div_mul_cancel (p.denominator_dvd o)
  have hdiv' : ((p.denominator / (p.weight o).den : ℕ) : ℚ) * (p.weight o).den = p.denominator := by
    exact_mod_cast hdiv
  have hnum' : ((p.weight o).num.toNat : ℚ) = (p.weight o).num := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [copies, Nat.cast_mul, hnum']
  rw [← Rat.mul_den_eq_num]
  calc
    _ = (((p.denominator / (p.weight o).den : ℕ) : ℚ) * (p.weight o).den) * p.weight o := by ring
    _ = _ := by rw [hdiv']

lemma total_copies (p : RationalLaw O) : ∑ o, p.copies o = p.denominator := by
  have h : (∑ o, (p.copies o : ℚ)) = p.denominator := by
    simp_rw [p.copies_eq]
    rw [← Finset.mul_sum, p.total, mul_one]
  exact_mod_cast h

abbrev Expanded (p : RationalLaw O) := Σ o : O, Fin (p.copies o)

lemma card_expanded (p : RationalLaw O) : Fintype.card p.Expanded = p.denominator := by
  simp only [Expanded, Fintype.card_sigma, Fintype.card_fin, p.total_copies]

noncomputable instance expandedNonempty (p : RationalLaw O) : Nonempty p.Expanded :=
  Fintype.card_pos_iff.mp (by rw [p.card_expanded]; exact p.denominator_pos)

lemma copies_real (p : RationalLaw O) (o : O) :
    (p.copies o : ℝ) = p.denominator * (p.weight o : ℝ) := by
  exact_mod_cast p.copies_eq o

theorem expect_expanded (p : RationalLaw O) (f : O → ℝ) :
    (𝔼 v : p.Expanded, f v.1) = ∑ o, (p.weight o : ℝ) * f o := by
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, p.card_expanded]
  simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, p.copies_real, mul_assoc, ← Finset.mul_sum]
  have h : (p.denominator : ℝ) ≠ 0 := by exact_mod_cast p.denominator_pos.ne'
  field_simp

abbrev Vertices (p : RationalLaw O) (C : Type*) (n : ℕ) := (Fin n → C) × p.Expanded

lemma card_vertices (p : RationalLaw O) (C : Type*) [Fintype C] (n : ℕ) :
    Fintype.card (p.Vertices C n) = Fintype.card C ^ n * p.denominator := by
  simp only [Vertices, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, p.card_expanded]

lemma expect_vertices (p : RationalLaw O) {C : Type*} [Fintype C] (n : ℕ)
    (f : (Fin n → C) → O → ℝ) :
    (𝔼 v : p.Vertices C n, f v.1 v.2.1) =
      𝔼 c : Fin n → C, ∑ o, (p.weight o : ℝ) * f c o := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  congr 1; funext c
  exact p.expect_expanded (f c)

end RationalLaw

theorem density_le_location_square {V X : Type*} [Fintype V] (A : Finset V)
    (location : V → X) (f : X → ℝ) (hA : ∀ v ∈ A, f (location v) = 1) :
    (A.card : ℝ) / Fintype.card V ≤ 𝔼 v, (f (location v))^2 := by
  have hp (v : V) : (if v ∈ A then (1:ℝ) else 0) ≤ (f (location v))^2 := by
    by_cases hv : v ∈ A
    · simp [hv,hA v hv]
    · simp only [ite_eq_right hv]; positivity
  have h := Finset.expect_le_expect (fun v (_ : v ∈ Finset.univ) => hp v)
  simpa only [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_univ,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using h

theorem density_from_good_fibers {C B V : Type*} [Fintype C] [Nonempty C]
    [Fintype B] [Fintype V]
    (p : RationalLaw B) (bad : C → B → Prop) (density : C → B → ℝ)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 8*ε < δ)
    (hbad : (𝔼 c, ∑ b, (p.weight b : ℝ) * (if bad c b then 1 else 0)) ≤ 2*ε)
    (hgood : ∀ c b, ¬bad c b → density c b ≤ 6*ε)
    (hone : ∀ c b, density c b ≤ 1) (A : Finset V)
    (haverage : (A.card : ℝ) / Fintype.card V ≤
      𝔼 c, ∑ b, (p.weight b : ℝ) * density c b) :
    (A.card : ℝ) / Fintype.card V < δ := by
  have hp (c : C) (b : B) : density c b ≤ 6*ε + (if bad c b then 1 else 0) := by
    by_cases h : bad c b
    · simp only [ite_eq_left h]; linarith [hone c b]
    · simpa only [ite_eq_right h,add_zero] using hgood c b h
  have ht : (∑ b, (p.weight b : ℝ)) = 1 := by exact_mod_cast p.total
  have hsum (c : C) : (∑ b, (p.weight b : ℝ) * density c b) ≤
      6*ε + ∑ b, (p.weight b : ℝ) * (if bad c b then 1 else 0) := by
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
      mul_le_mul_of_nonneg_left (hp c b) (by exact_mod_cast p.nonneg b : (0:ℝ) ≤ p.weight b))
    simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht, one_mul] using h
  have hmean := Finset.expect_le_expect (fun c (_ : c ∈ Finset.univ) => hsum c)
  rw [Finset.expect_add_distrib, Fintype.expect_const] at hmean
  linarith

end LargeIndependentSets

end OAI
