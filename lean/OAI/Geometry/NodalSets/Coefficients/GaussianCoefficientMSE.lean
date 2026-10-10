import OAI.Geometry.NodalSets.Waves.RescaledGaussianField

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_square_integral (z : ι → ℂ) :
    ∫ coeff, (pairLinearSum z coeff)^2 ∂gaussianPairs = ∑ i, ‖z i‖^2 := by
  have hc : Continuous (pairLinearSum z) := by unfold pairLinearSum; fun_prop
  have hh := variance_eq_integral (μ := gaussianPairs) hc.measurable.aemeasurable
  rw [pairLinearSum_mean] at hh
  simp only [sub_zero] at hh
  rw [← hh,variance_pairLinearSum]

lemma gaussianWaveField_sub_pair (V W : ι → Coord → ℂ) (x : Coord)
    (coeff : ι × Fin 2 → ℝ) :
    gaussianWaveField V coeff x-gaussianWaveField W coeff x =
      pairLinearSum (fun i ↦ V i x-W i x) coeff := by
  rw [pairLinearSum_eq_complex]
  simp only [gaussianWaveField,Complex.re_sum,mul_sub,Complex.sub_re,Finset.sum_sub_distrib]

lemma gaussianWaveField_difference_mse (V W : ι → Coord → ℂ) (x : Coord) :
    ∫ coeff, (gaussianWaveField V coeff x-gaussianWaveField W coeff x)^2 ∂gaussianPairs =
      ∑ i, ‖V i x-W i x‖^2 := by
  simp_rw [gaussianWaveField_sub_pair]
  exact pairLinearSum_square_integral _

lemma rescaledGaussianField_centered_mse (V W : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s sigma : ℝ) (x v : Coord) :
    ∫ coeff, (rescaledGaussianField V S0 T0 S N s sigma x coeff v -
      rescaledSeed S0 T0 S N s sigma x v-gaussianWaveField W coeff v)^2 ∂gaussianPairs =
      ∑ i, ‖normalizedRescaling (V i) S N s sigma x v-W i v‖^2 := by
  simp_rw [rescaledGaussianField_decomposition,add_sub_cancel_left]
  exact gaussianWaveField_difference_mse _ W v

end
end Yau.Geometry

end OAI
