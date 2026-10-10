import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.RationalLaw

namespace OAI

namespace LargeIndependentSets.RationalLaw
open scoped BigOperators Classical
variable {I : Type*} [Fintype I]

noncomputable def uniform (I : Type*) [Fintype I] [Nonempty I] : RationalLaw I where
  weight _ := 1 / Fintype.card I
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card I : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

noncomputable def bind (p : RationalLaw I) {J : I → Type*} [∀ i, Fintype (J i)]
    (q : ∀ i, RationalLaw (J i)) : RationalLaw (Sigma J) where
  weight o := p.weight o.1 * (q o.1).weight o.2
  nonneg o := mul_nonneg (p.nonneg _) ((q _).nonneg _)
  total := by
    simp only [Fintype.sum_sigma, ← Finset.mul_sum, fun i => (q i).total, mul_one]
    exact p.total

noncomputable def pi [DecidableEq I] {J : I → Type*} [∀ i, Fintype (J i)]
    (q : ∀ i, RationalLaw (J i)) : RationalLaw (∀ i, J i) where
  weight x := ∏ i, (q i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (q i).nonneg _)
  total := by
    rw [← Fintype.prod_sum]
    simp only [fun i => (q i).total, Finset.prod_const_one]

lemma expect_uniform (f : I → ℝ) [Nonempty I] :
    (∑ i, ((uniform I).weight i : ℝ) * f i) = 𝔼 i, f i := by
  simp only [uniform, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    Finset.expect_eq_sum_div_card, Finset.card_univ, ← Finset.mul_sum]
  ring

lemma expect_bind (p : RationalLaw I) {J : I → Type*} [∀ i, Fintype (J i)]
    (q : ∀ i, RationalLaw (J i)) (f : Sigma J → ℝ) :
    (∑ o, ((p.bind q).weight o : ℝ) * f o) =
      ∑ i, (p.weight i : ℝ) * ∑ j, ((q i).weight j : ℝ) * f ⟨i,j⟩ := by
  simp only [bind, Fintype.sum_sigma, Rat.cast_mul, mul_assoc, Finset.mul_sum]

end LargeIndependentSets.RationalLaw

end OAI
