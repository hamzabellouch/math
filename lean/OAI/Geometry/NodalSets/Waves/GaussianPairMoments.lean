import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientMSE

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_memLp_two (z : ι → ℂ) : MemLp (pairLinearSum z) 2 gaussianPairs := by
  classical
  unfold pairLinearSum gaussianPairs
  apply memLp_finsetSum
  intro p _
  have hh : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := IsGaussian.memLp_two_id
  exact (hh.comp_measurePreserving (measurePreserving_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1) p)).const_mul _

lemma pairLinearSum_mean_square (z : ι → ℂ) (m : ℝ) :
    ∫ coeff, (m+pairLinearSum z coeff)^2 ∂gaussianPairs = m^2+∑ i, ‖z i‖^2 := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  have hp := pairLinearSum_memLp_two z
  have hh := variance_eq_sub ((memLp_const m).add hp)
  have hm : ∫ coeff, m+pairLinearSum z coeff ∂gaussianPairs = m := by
    rw [integral_add (integrable_const _) (pairLinearSum_integrable z),pairLinearSum_mean,integral_const]
    simp
  change Var[fun coeff ↦ m+pairLinearSum z coeff;gaussianPairs] =
    (∫ coeff, (m+pairLinearSum z coeff)^2 ∂gaussianPairs) -
      (∫ coeff, m+pairLinearSum z coeff ∂gaussianPairs)^2 at hh
  rw [hm,variance_const_add hp.aestronglyMeasurable,variance_pairLinearSum] at hh
  linarith

lemma rescaledGaussianField_mse (V W : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s sigma : ℝ) (x v : Coord) :
    ∫ coeff, (rescaledGaussianField V S0 T0 S N s sigma x coeff v -
      gaussianWaveField W coeff v)^2 ∂gaussianPairs =
      (rescaledSeed S0 T0 S N s sigma x v)^2 +
        ∑ i, ‖normalizedRescaling (V i) S N s sigma x v-W i v‖^2 := by
  have heq (coeff : ι × Fin 2 → ℝ) :
      rescaledGaussianField V S0 T0 S N s sigma x coeff v - gaussianWaveField W coeff v =
        rescaledSeed S0 T0 S N s sigma x v +
          pairLinearSum (fun i ↦ normalizedRescaling (V i) S N s sigma x v-W i v) coeff := by
    rw [rescaledGaussianField_decomposition,← gaussianWaveField_sub_pair]
    ring
  simp_rw [heq]
  exact pairLinearSum_mean_square _ _

end
end Yau.Geometry

end OAI
