import OAI.NumberTheory.TwoPoint.Bounds.ObservedDesignationWeights

namespace OAI

/-! Extra-reciprocal estimates require the lower prime bound only on used tuple coordinates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma designation_sdiff_decidable {τ : Type*} (d₁ d₂ : DecidableEq τ) (S U : Finset τ) :
    @SDiff.sdiff (Finset τ) (@Finset.instSDiff τ d₁) S U =
      @SDiff.sdiff (Finset τ) (@Finset.instSDiff τ d₂) S U := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  rfl

theorem full_word_designated_reciprocal_bound_on_support {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (label : τ → ι) (U : Finset τ) (hU : U ⊆ nonsingletonSlots label)
    (p : ι → ℕ) (H : ℝ) (hH : 0 < H)
    (hp : ∀ i ∈ nonsingletonLabels label, H ≤ p i) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label ≤
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^
        (∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card) := by
  have he : designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label =
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) *
        ∏ i ∈ nonsingletonLabels label, (p i : ℝ)⁻¹ ^
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card := by
    simpa only [designationLit_unlit label U hU, designationLit_lit, designatedReciprocal] using
      observed_designation_reciprocal_factor label (designationLit U) (fun i => (p i : ℝ))
  rw [he, ← prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply prod_le_prod₀
  · intro i _
    positivity
  · intro i hi
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hH (hp i hi)) _

end TwoPointCorrelations

end OAI
