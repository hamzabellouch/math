import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology Set

theorem exterior_integral_tendsto_zero {d : ℕ} (μ : Measure (Ambient d))
    (a : Ambient d) (f : Ambient d → ℝ)
    (hi : IntegrableOn f (closedExterior a 1) μ) :
    Tendsto (fun j : ℕ => ∫ x in closedExterior a ((j : ℝ) + 2), f x ∂μ)
      atTop (𝓝 0) := by
  have hanti : Antitone (fun j : ℕ => closedExterior a ((j : ℝ) + 2)) := by
    intro i j hij x hx
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    change (i : ℝ) + 2 ≤ dist a x
    change (j : ℝ) + 2 ≤ dist a x at hx
    linarith
  have hempty : (⋂ j : ℕ, closedExterior a ((j : ℝ) + 2)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨j, hj⟩ := exists_nat_gt (dist a x)
    have hxj : (j : ℝ) + 2 ≤ dist a x := Set.mem_iInter.mp hx j
    linarith
  have hi0 : IntegrableOn f (closedExterior a ((0 : ℝ) + 2)) μ := by
    apply hi.mono_set
    intro x hx
    change 1 ≤ dist a x
    change (0 : ℝ) + 2 ≤ dist a x at hx
    linarith
  simpa only [hempty, setIntegral_empty] using! tendsto_setIntegral_of_antitone
    (fun j : ℕ => closedExterior_measurable a ((j : ℝ) + 2)) hanti ⟨0, by simpa using! hi0⟩

end

end RieszRectifiability

end OAI
