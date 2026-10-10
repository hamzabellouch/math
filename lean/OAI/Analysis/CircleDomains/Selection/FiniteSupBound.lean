import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace OAI

/-! A simultaneous finite weighted bound survives taking the independent
supremum in each coordinate. This will bound every tail of the fusion tree. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem finite_weighted_sup_le {I Z : Type*} [Fintype I]
    (D : I → Set Z) (f : I → Z → ℝ) (w : I → ℝ)
    (hne : ∀ i, (D i).Nonempty)
    (hw : ∀ i, 0 ≤ w i) (hw1 : (∑ i, w i) = 1) {b : ℝ}
    (hbound : ∀ z : I → Z, (∀ i, z i ∈ D i) → ∑ i, w i * f i (z i) ≤ b) :
    ∑ i, w i * sSup (f i '' D i) ≤ b := by
  classical
  by_contra h
  let δ := ((∑ i, w i * sSup (f i '' D i)) - b) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hnear (i : I) : ∃ z ∈ D i, sSup (f i '' D i) - δ < f i z := by
    obtain ⟨v, ⟨z, hz, rfl⟩, hv⟩ := exists_lt_of_lt_csSup ((hne i).image (f i))
      (sub_lt_self _ hδ)
    exact ⟨z, hz, hv⟩
  choose z hzD hz using hnear
  have hs : (∑ i, w i * sSup (f i '' D i)) - δ ≤ b := calc
    (∑ i, w i * sSup (f i '' D i)) - δ =
        ∑ i, w i * (sSup (f i '' D i) - δ) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ i, w i * f i (z i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz i).le (hw i)
    _ ≤ b := hbound z hzD
  dsimp [δ] at hs
  linarith

end CircleDomainRigidity

end

end OAI
