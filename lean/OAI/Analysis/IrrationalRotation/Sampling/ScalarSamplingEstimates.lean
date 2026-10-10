import OAI.Analysis.IrrationalRotation.Model.ScalarSamplingEstimates
import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Analysis.ScalarKernelEstimates
import OAI.Analysis.IrrationalRotation.Sampling.UniformIntervalPhase

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem all_kernel_estimates : AllKernelEstimates := by
  intro m hm
  exact ⟨manuscriptKernel_estimates hm, manuscriptEndpointKernel_estimates hm⟩

theorem all_marginal_estimates : AllMarginalEstimates := by
  intro N₀ n hN hn
  exact UniformIntervalPhase.scalar_marginal N₀ n hN hn

theorem kernel_and_marginal_estimates : AllKernelEstimates ∧ AllMarginalEstimates :=
  ⟨all_kernel_estimates, all_marginal_estimates⟩

theorem parameter_kernel_eq_manuscript {m : ℕ} (hm : 200 ≤ m) (z : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    CircleParameterData.kernel m z v = manuscriptKernel m z v := by
  rw [manuscriptKernel, circleKernel_eq_raw_on_unit (manuscript_parameters hm).2.1 z hv]
  unfold CircleParameterData.kernel CircleParameterData.delta CircleParameterData.kernelWidth
    rawKernel delta
  simp only [Set.indicator_apply, mem_Ioo, ite_and, one_div]

theorem parameter_orientedKernel_eq {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (z : ℝ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    CircleParameterData.orientedKernel endpoint m z v =
      if endpoint then manuscriptEndpointKernel m z v else manuscriptKernel m z v := by
  cases endpoint <;>
    simp only [CircleParameterData.orientedKernel, Bool.false_eq_true, ite_false, ite_true]
  · exact parameter_kernel_eq_manuscript hm z hv
  · exact parameter_kernel_eq_manuscript hm (z - v) hv

theorem parameter_samplingAverage_eq (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 200 ≤ p.m j) (endpoint : Bool) (x : Circle) :
    p.samplingAverage θ j r endpoint x =
      (1 / ((p.samples j r).card : ℝ)) *
        ∑ n ∈ p.samples j r, ∏ i ∈ p.block j,
          if endpoint then manuscriptEndpointKernel (p.m j) (p.coordinate i x)
            (Int.fract ((n : ℝ) * p.alpha θ i))
          else manuscriptKernel (p.m j) (p.coordinate i x)
            (Int.fract ((n : ℝ) * p.alpha θ i)) := by
  unfold CircleParameterData.samplingAverage
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  exact parameter_orientedKernel_eq hm endpoint _
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

end Invariant233.ScalarSampling

end

end OAI
