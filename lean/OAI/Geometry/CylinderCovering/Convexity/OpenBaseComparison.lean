import OAI.Geometry.CylinderCovering.Convexity.OpenBaseApproximationDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

theorem Cylinder.shadowArea_eq_of_axis_eq {C D : Cylinder}
    (haxis : D.axis = C.axis) (S : Set Space) : D.shadowArea S = C.shadowArea S := by
  rcases C with ⟨u, hu, B⟩
  rcases D with ⟨v, hv, A⟩
  change v = u at haxis
  subst v
  rfl

theorem familyRelativeArea_le {n : ℕ} (C : Fin n → Cylinder) (S : Set Space)
    {m : ℝ} (hm : 0 < m) (hshadow : ∀ i, m ≤ (C i).shadowArea S) :
    familyRelativeArea C S ≤ familyArea C / m := by
  unfold familyRelativeArea familyArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hm (hshadow i)

theorem familyRelativeArea_lt_half {n : ℕ} (C : Fin n → Cylinder) (S : Set Space)
    {m : ℝ} (hm : 0 < m) (hshadow : ∀ i, m ≤ (C i).shadowArea S)
    (hcost : familyArea C < m / 2) : familyRelativeArea C S < 1 / 2 := by
  apply (familyRelativeArea_le C S hm hshadow).trans_lt
  rw [div_lt_iff₀ hm]
  linarith

end RuledApproximation

end

end OAI
