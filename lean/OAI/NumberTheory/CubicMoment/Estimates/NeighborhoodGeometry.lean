import OAI.NumberTheory.CubicMoment.Estimates.DominantNeighborhood

namespace OAI

/-! Quantitative room for the first exceptional conductor neighborhood. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventual_first_neighborhood_rows :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (Y κ N : ℝ), T ≤ Y → κ ≤ 1/10000 →
      Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → ∀ a : Eisenstein, gramDyad N a →
      primary a ∧ Squarefree a ∧ norm a ≤ Y^(1001/1000:ℝ) ∧
        Y^(1/1000:ℝ) ≤ norm a := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/10000 by norm_num)).eventually_ge_atTop 2)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y κ N hY hκ hNlo hNhi a ha
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  refine ⟨ha.1,ha.2.1,?_,?_⟩
  · calc
      norm a ≤ 2*N := ha.2.2.2.le
      _ ≤ 2*Y^(1+κ) := by gcongr
      _ ≤ Y^(9/10000:ℝ)*Y^(1+κ) :=
        mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY))
          (Real.rpow_nonneg hYp.le _)
      _ = Y^(9/10000+(1+κ)) := (Real.rpow_add hYp _ _).symm
      _ ≤ Y^(1001/1000:ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  · exact (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith : (1/1000:ℝ) ≤ 1-κ)).trans
      (hNlo.trans ha.2.2.1)

end CubicFirstMoment

end

end OAI
