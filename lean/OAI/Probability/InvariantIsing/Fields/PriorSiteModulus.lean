import OAI.Probability.InvariantIsing.Arrays.TensorSiteMean
import OAI.Probability.InvariantIsing.Fields.PriorTensorMinimum

namespace OAI

/-! Continuity in the finite ordinary-field variances for an actual
fixed spin/leaf prior, uniformly in its spin constraints. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology NNReal
namespace InvariantIsing

lemma prior_site_pressure_modulus
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (d : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (mono : Fin (n+1) → Fin k → ℝ≥0) (a b : Fin (n+1) → ℝ≥0) :
    |(N : ℝ)⁻¹*(∫ p, priorTensorLog ν eig c I d amp
        (fun i => tensorVarianceProfile I d (a i) (mono i)) p ∂μ.prod gaussianCoordinates) -
      (N : ℝ)⁻¹*(∫ p, priorTensorLog ν eig c I d amp
        (fun i => tensorVarianceProfile I d (b i) (mono i)) p ∂μ.prod gaussianCoordinates)| ≤
      2*∑ i, |(NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)| *
        ((NNReal.sqrt (a i) : ℝ)+(NNReal.sqrt (b i) : ℝ)) := by
  let F := fun (a : Fin (n+1) → ℝ≥0) => priorTensorLog ν eig c I d amp
    (fun i => tensorVarianceProfile I d (a i) (mono i))
  let M := ∑ i, |(NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)| *
    ((NNReal.sqrt (a i) : ℝ)+(NNReal.sqrt (b i) : ℝ))
  have hi x : Integrable (F x) (μ.prod gaussianCoordinates) :=
    priorTensorLog_integrable hhaar hgauss hN μ hμ ν eig c I d amp x mono
  have hp (U : SpecialOrthogonal N) :
      |(∫ z, F a (U,z) ∂gaussianCoordinates)-∫ z, F b (U,z) ∂gaussianCoordinates| ≤ 2*((N : ℝ)*M) :=
    tensorSiteLogMean_modulus (specialRotation U) I d amp a b mono ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1+fieldEnergy c x.1)
      (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy eig (specialRotation U) σ+fieldEnergy c σ))
  change |(N : ℝ)⁻¹*(∫ p, F a p ∂_)-(N : ℝ)⁻¹*(∫ p, F b p ∂_)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)),
    integral_prod _ (hi a), integral_prod _ (hi b),
    ← integral_sub (hi a).integral_prod_left (hi b).integral_prod_left]
  have hv := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => (∫ z, F a (U,z) ∂gaussianCoordinates)-∫ z, F b (U,z) ∂gaussianCoordinates)
    (C := 2*((N : ℝ)*M))
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hp U)
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at hv
  refine (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq ?_
  have hnz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp only [M]
  field_simp

lemma continuous_prior_site_pressure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (d : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (mono : Fin (n+1) → Fin k → ℝ≥0) :
    Continuous (fun a : Fin (n+1) → ℝ≥0 => (N : ℝ)⁻¹*∫ p, priorTensorLog ν eig c I d amp
      (fun i => tensorVarianceProfile I d (a i) (mono i)) p ∂μ.prod gaussianCoordinates) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let M := fun a : Fin (n+1) → ℝ≥0 => 2*∑ i,
    |(NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)| *
      ((NNReal.sqrt (a i) : ℝ)+(NNReal.sqrt (b i) : ℝ))
  have hM : Continuous M := by fun_prop
  have hz : M b=0 := by simp [M]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using prior_site_pressure_modulus hhaar hgauss hN μ hμ ν eig c I d amp mono a b)
  simpa only [hz] using hM.tendsto b

end InvariantIsing

end

end OAI
