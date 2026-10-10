import Mathlib.Analysis.ODE.PicardLindelof

namespace OAI

/-! A small smooth-ODE bridge for the explicit exterior profile. -/

open Set
open scoped ContDiff
namespace DefocusingNLS

theorem spectralODE_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → E → E) (v : ℝ → E)
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hv : ∀ x, HasDerivAt v (F x (v x)) x) : ContDiff ℝ ∞ v := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h : ContDiffOn ℝ ∞ v (Icc (x-1) (x+1)) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := F) (u := (univ : Set E)) hF.contDiffOn
    · exact fun t _ => (hv t).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
  exact h.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

end DefocusingNLS

end OAI
