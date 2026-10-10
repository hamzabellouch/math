import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ComplexHeightPairing

namespace OAI

/-!
# Removing the complex interior cutoff

The hard-truncated complex height integrand is the indicator restriction of the
full interior integrand to pairs separated by at least the truncation radius.
Integrability of the full integrand then yields convergence of the truncated
pair integrals as the radii tend to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem complex_height_interior_cutoff_eq_indicator {d : ℕ}
    (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ) (g : Ambient d → ℂ) :
    (fun q : Ambient d × Ambient d => (w q.1 - w q.2) •
      (symmetricFractionalCutoffKernel m ε q • (g q.1 - g q.2))) =
      {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2}.indicator
        (complexHeightInteriorIntegrand m w g) := by
  funext q
  by_cases h : ε ≤ dist q.1 q.2
  · rw [indicator_of_mem (show q ∈ {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2} from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_left h, complexHeightInteriorIntegrand]
  · rw [indicator_of_notMem (show q ∉ {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2} from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_right h]
    exact (congrArg (fun z : ℂ => (w q.1 - w q.2) • z)
      (zero_smul ℝ (g q.1 - g q.2))).trans (smul_zero (w q.1 - w q.2))

theorem complex_height_interior_cutoff_integral_tendsto {d : ℕ}
    (m : ℕ) (ν : Measure (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hi : Integrable (complexHeightInteriorIntegrand m w g) (ν.prod ν))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) •
      (symmetricFractionalCutoffKernel m (ε j) q • (g q.1 - g q.2)) ∂ν.prod ν)
      atTop (𝓝 (∫ q, complexHeightInteriorIntegrand m w g q ∂ν.prod ν)) := by
  let F := complexHeightInteriorIntegrand m w g
  let S := fun j => {q : Ambient d × Ambient d | ε j ≤ dist q.1 q.2}
  have hS (j : ℕ) : MeasurableSet (S j) :=
    measurableSet_le measurable_const (continuous_fst.dist continuous_snd).measurable
  have hlim (q : Ambient d × Ambient d) :
      Tendsto (fun j => (S j).indicator F q) atTop (𝓝 (F q)) := by
    by_cases hd : q.1 = q.2
    · have hF : F q = 0 := by
        dsimp only [F, complexHeightInteriorIntegrand]
        rw [hd, sub_self]
        exact zero_smul ℝ _
      have hz : (fun j => (S j).indicator F q) = fun _ : ℕ => (0 : ℂ) := by
        funext j
        by_cases hs : q ∈ S j
        · exact (indicator_of_mem hs F).trans hF
        · exact indicator_of_notMem hs F
      rw [hz, hF]
      exact tendsto_const_nhds
    · have hp := dist_pos.mpr hd
      apply tendsto_const_nhds.congr'
      filter_upwards [hε.eventually (gt_mem_nhds hp)] with j hj
      exact (indicator_of_mem (show q ∈ S j from hj.le) F).symm
  have ht := tendsto_integral_of_dominated_convergence (fun q => ‖F q‖)
    (fun j => hi.aestronglyMeasurable.indicator (hS j)) hi.norm
    (fun j => Eventually.of_forall fun q => norm_indicator_le_norm_self F q)
    (Eventually.of_forall hlim)
  have heq : (fun j => ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) •
      (symmetricFractionalCutoffKernel m (ε j) q • (g q.1 - g q.2)) ∂ν.prod ν) =
      fun j => ∫ q, (S j).indicator F q ∂ν.prod ν := by
    funext j
    rw [complex_height_interior_cutoff_eq_indicator]
  rw [heq]
  exact ht

end

end RieszRectifiability

end OAI
