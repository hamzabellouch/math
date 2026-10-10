import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.ConditionalCentered
import OAI.Probability.BinarySweep.Trajectories.PathSign
import OAI.Probability.BinarySweep.FiniteLaws.RemainingSign

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma conditional_full_sign (z : ℝ) :
    (∑g : ConditionalChoices H, conditionalChoiceWeight H z g*realSign (gridSweep bits g.val)) =
      (∑g : GridChoices bits, if pathEvent H g then
        gridWeight bits z g*realSign (gridSweep bits g) else 0)/conditionalNormalizer H z := by
  unfold conditionalChoiceWeight
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div]
  congr 1
  have he := sum_dite_zero (pathEvent H)
    (fun g _ => gridWeight bits z g*realSign (gridSweep bits g))
  refine Eq.trans ?_ he.symm
  apply Finset.sum_congr
  · ext g; simp only [Finset.mem_univ]
  intro g _
  rfl

theorem conditional_sign_zero (z : ℝ)
    (hs : (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    (∑a, conditionalGroupLaw H z a*realSign a)=0 := by
  change (∑a, conditionalGroupLaw H z a • realSign a)=0
  rw [conditionalGroupLaw_expectation]
  by_cases hn : Nonempty (ConditionalChoices H)
  · obtain ⟨g₀⟩ := hn
    simp only [smul_eq_mul]
    have he (g : ConditionalChoices H) :
        conditionalChoiceWeight H z g *
          (realSign (remainingPerm H g₀.val g₀.property)/realSign (gridSweep bits g₀.val)*
            realSign (gridSweep bits g.val)) =
        (realSign (remainingPerm H g₀.val g₀.property)/realSign (gridSweep bits g₀.val))*
          (conditionalChoiceWeight H z g*realSign (gridSweep bits g.val)) := by ring
    have hf (g : ConditionalChoices H) :
        conditionalChoiceWeight H z g*realSign (remainingPerm H g.val g.property) =
        (realSign (remainingPerm H g₀.val g₀.property)/realSign (gridSweep bits g₀.val))*
          (conditionalChoiceWeight H z g*realSign (gridSweep bits g.val)) := by
      rw [remaining_realSign_factor H g g₀]
      exact he g
    simp_rw [hf]
    rw [←Finset.mul_sum,conditional_full_sign H z,hs,zero_div,mul_zero]
  · have : IsEmpty (ConditionalChoices H) := not_nonempty_iff.mp hn
    exact Finset.sum_eq_zero (fun g _ => isEmptyElim g)

lemma conditional_sign_zero_empty (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (y : GridOutside bits j) (hy : lineHoles H j y=0) :
    (∑a, conditionalGroupLaw H z a*realSign a)=0 :=
  conditional_sign_zero H z (signed_path_weight_zero_empty H z j hj y hy)

lemma conditional_sign_zero_uniform (j : Fin b) (y : GridOutside bits j)
    {u v : Slot (bits j)} (huv : u≠v)
    (hu : u∉Set.range (lineOutput H j y)) (hv : v∉Set.range (lineOutput H j y)) :
    (∑a, conditionalGroupLaw H 0 a*realSign a)=0 :=
  conditional_sign_zero H 0 (signed_path_weight_zero_uniform H j y huv hu hv)

end BinaryCoordinateSweeps

end

end OAI
