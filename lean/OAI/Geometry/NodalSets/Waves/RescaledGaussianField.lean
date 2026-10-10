import OAI.Geometry.NodalSets.Elliptic.NormalizedRescaling
import OAI.Geometry.NodalSets.Waves.LatticeValueVariance

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

def rescaledGaussianField (V : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s σ : ℝ) (x : Coord) (coeff : ι × Fin 2 → ℝ) (v : Coord) : ℝ :=
  (oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v)+
    gaussianWaveField V coeff (x+(N*s)⁻¹ • v)) /
      (σ*Real.exp (fderiv ℝ S x v/s))

lemma rescaledGaussianField_decomposition (V : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s σ : ℝ) (x : Coord) (coeff : ι × Fin 2 → ℝ) (v : Coord) :
    rescaledGaussianField V S0 T0 S N s σ x coeff v = rescaledSeed S0 T0 S N s σ x v +
      gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s σ x) coeff v := by
  classical
  simp only [rescaledGaussianField,rescaledSeed,add_div,gaussianWaveField,
    normalizedRescaling_eq_div,← mul_div_assoc,Complex.re_sum,Complex.div_ofReal_re,
    Finset.sum_div]

lemma pairLinearSum_integrable (z : ι → ℂ) : Integrable (pairLinearSum z) gaussianPairs := by
  classical
  unfold pairLinearSum gaussianPairs
  apply integrable_finsetSum
  intro p _
  exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
    (i := p) IsGaussian.integrable_id).const_mul _

lemma pairLinearSum_mean (z : ι → ℂ) : ∫ coeff, pairLinearSum z coeff ∂gaussianPairs = 0 := by
  classical
  unfold pairLinearSum gaussianPairs
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro p _
    rw [integral_const_mul,integral_eval]
    simp
  · intro p _
    exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
      (i := p) IsGaussian.integrable_id).const_mul _

lemma rescaledGaussianField_mean (V : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s σ : ℝ) (x v : Coord) :
    ∫ coeff, rescaledGaussianField V S0 T0 S N s σ x coeff v ∂gaussianPairs =
      rescaledSeed S0 T0 S N s σ x v := by
  classical
  let Z := fun i ↦ normalizedRescaling (V i) S N s σ x v
  have he : (fun coeff ↦ gaussianWaveField
      (fun i ↦ normalizedRescaling (V i) S N s σ x) coeff v) = pairLinearSum Z := by
    funext coeff
    rw [pairLinearSum_eq_complex]
    simp only [gaussianWaveField,Complex.re_sum,Z]
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by
    unfold gaussianPairs
    infer_instance
  simp_rw [rescaledGaussianField_decomposition]
  change ∫ coeff, rescaledSeed S0 T0 S N s σ x v+
    (fun coeff ↦ gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s σ x) coeff v) coeff
    ∂gaussianPairs = _
  rw [he,integral_add (integrable_const _) (pairLinearSum_integrable Z),
    pairLinearSum_mean,add_zero,integral_const]
  simp

end
end Yau.Geometry

end OAI
