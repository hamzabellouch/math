import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ScalarRieszTestBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

def scalarRieszSchwartzTest {d : ℕ} (m : ℕ) (e : Ambient d)
    (g : 𝓢(Ambient d, ℝ)) (x : Ambient d) : ℝ :=
  (-1 / 2 : ℝ) * ∫ h, symmetricScalarRieszTestKernel m e g x h

theorem symmetricScalarCappedTestKernel_tendsto {d : ℕ} (m : ℕ)
    (e : Ambient d) (g : Ambient d → ℝ) (x h : Ambient d)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => symmetricScalarCappedTestKernel m e (ε j) g x h) atTop
      (𝓝 (symmetricScalarRieszTestKernel m e g x h)) := by
  by_cases hh : h = 0
  · subst h
    simpa only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel,
      inner_zero_right, zero_mul, mul_zero] using!
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  apply tendsto_const_nhds.congr'
  filter_upwards [hε.eventually (gt_mem_nhds hn)] with j hj
  simp only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel,
    cappedInverseDistancePow, inverseDistancePow, dist_zero_left, max_eq_right hj.le]

theorem scalarCappedTransform_tendsto_schwartz (p : ℕ)
    (e : Ambient (p + 1)) (g : 𝓢(Ambient (p + 1), ℝ)) (x : Ambient (p + 1))
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => scalarCappedTransform (p + 1) volume e (ε j) g x) atTop
      (𝓝 (scalarRieszSchwartzTest (p + 1) e g x)) := by
  have hI := symmetricScalarRieszTestKernel_integrable p _ volume
    (volume_global_upper_growth (p + 1)) e g x
  have hsym (j : ℕ) := scalarCappedTransform_symmetric_identity (p + 1) e (ε j)
    (hεpos j) g g.continuous.measurable g.integrable x
  have hlim := tendsto_integral_of_dominated_convergence
    (fun h => ‖symmetricScalarRieszTestKernel (p + 1) e g x h‖)
    (fun j => (hsym j).1.aestronglyMeasurable) hI.norm
    (fun j => Eventually.of_forall fun h =>
      symmetricScalarCappedTestKernel_norm_le (p + 1) e (ε j) g x h)
    (Eventually.of_forall fun h => symmetricScalarCappedTestKernel_tendsto (p + 1) e g x h ε hε)
  have hm := hlim.const_mul (-1 / 2 : ℝ)
  apply hm.congr'
  exact Eventually.of_forall fun j => (hsym j).2.symm

end

end RieszRectifiability

end OAI
