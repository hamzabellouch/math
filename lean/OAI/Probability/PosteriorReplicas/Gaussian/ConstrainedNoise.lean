import OAI.Probability.PosteriorReplicas.Gaussian.ConstrainedGaussian
import OAI.Probability.PosteriorReplicas.Gaussian.MatrixNoise

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianResidualRows {m : ℕ} (v : Fin m → E) (k : ℕ) : Measure (Fin k → E) :=
  Measure.pi fun _ => (stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection

instance {m : ℕ} (v : Fin m → E) (k : ℕ) : IsProbabilityMeasure (gaussianResidualRows v k) := by
  let : IsProbabilityMeasure ((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  unfold gaussianResidualRows
  infer_instance

omit [MeasurableSpace E] [BorelSpace E] in
lemma pairings_lift_residual {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v)
    (y : Fin m → ℝ) (R : E) :
    (fun i => ⟪v i, pairingLift v y + (Submodule.span ℝ (Set.range v))ᗮ.starProjection R⟫) = y := by
  funext i
  rw [inner_add_right, congrFun (pairings_pairingLift hv y) i]
  have hzero : ⟪v i, (Submodule.span ℝ (Set.range v))ᗮ.starProjection R⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) (by simp)
  rw [hzero, add_zero]

lemma constrained_gaussian_weighted_integral {m : ℕ} {v : Fin m → E}
    (hv : LinearIndependent ℝ v) (k : ℕ) {φ : (Fin k → Fin m → ℝ) → ℝ≥0∞}
    (hφ : Measurable φ) {g : (Fin k → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ A, φ (fun j i => ⟪v i, A j⟫) * g A ∂Measure.pi (fun _ => stdGaussian E) =
      ∫⁻ y, (∏ j, pairingsDensity v (y j)) * φ y *
        ∫⁻ R, g (fun j => pairingLift v (y j) + R j) ∂gaussianResidualRows v k ∂volume := by
  rw [constrained_gaussian_integral hv k (by fun_prop)]
  apply lintegral_congr
  intro y
  have he : (∫⁻ R, φ (fun j i => ⟪v i, pairingLift v (y j) + R j⟫) *
      g (fun j => pairingLift v (y j) + R j) ∂gaussianResidualRows v k) =
        φ y * ∫⁻ R, g (fun j => pairingLift v (y j) + R j) ∂gaussianResidualRows v k := by
    unfold gaussianResidualRows
    rw [← Measure.pi_map_pi (fun _ => (show Measurable
      (Submodule.span ℝ (Set.range v))ᗮ.starProjection by fun_prop).aemeasurable)]
    rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)]
    dsimp only [Function.comp_apply]
    have heq (R : Fin k → E) :
        (fun j i => ⟪v i, pairingLift v (y j) +
          (Submodule.span ℝ (Set.range v))ᗮ.starProjection (R j)⟫) = y := by
      funext j
      exact pairings_lift_residual hv (y j) (R j)
    simp_rw [heq]
    rw [lintegral_const_mul _ (by fun_prop)]
  change _ * (∫⁻ R, φ (fun j i => ⟪v i, pairingLift v (y j) + R j⟫) *
    g (fun j => pairingLift v (y j) + R j) ∂gaussianResidualRows v k) = _
  rw [he, mul_assoc]

lemma constrained_gaussian_noise_integral {m : ℕ} {v : Fin m → E}
    (hv : LinearIndependent ℝ v) (k n : ℕ) {g : (Fin k → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ A, matrixNoiseDensity m k n (fun i j => ⟪v i, A j⟫) * g A
      ∂Measure.pi (fun _ => stdGaussian E) =
      ∫⁻ z, ∫⁻ R, (∏ j, pairingsDensity v (fun i => noiseScale n * z i j)) *
        g (fun j => pairingLift v (fun i => noiseScale n * z i j) + R j)
          ∂gaussianResidualRows v k ∂matrixNormal m k := by
  have he (A : Fin k → E) : (fun i j => ⟪v i, A j⟫) =
      transposeCLE k m (fun j i => ⟪v i, A j⟫) := rfl
  simp_rw [he]
  rw [constrained_gaussian_weighted_integral hv k
    (φ := fun y => matrixNoiseDensity m k n (transposeCLE k m y)) (by fun_prop) hg]
  have hrw (y : Fin k → Fin m → ℝ) :
      (∏ j, pairingsDensity v (y j)) * matrixNoiseDensity m k n (transposeCLE k m y) *
        (∫⁻ R, g (fun j => pairingLift v (y j) + R j) ∂gaussianResidualRows v k) =
      matrixNoiseDensity m k n (transposeCLE k m y) *
        ((∏ j, pairingsDensity v (y j)) *
          ∫⁻ R, g (fun j => pairingLift v (y j) + R j) ∂gaussianResidualRows v k) := by ac_rfl
  simp_rw [hrw]
  rw [matrixNoise_transpose_lintegral (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [lintegral_const_mul _ (by fun_prop)]
  rfl

lemma constrained_gaussian_noise_limit {m : ℕ} {v : Fin m → E}
    (hv : LinearIndependent ℝ v) (k : ℕ) {g : (Fin k → E) → ℝ≥0∞} (hg : Continuous g)
    (b : ℝ≥0∞) (hb : b ≠ ∞) (hgb : ∀ A, g A ≤ b) :
    Tendsto (fun n => ∫⁻ A, matrixNoiseDensity m k n (fun i j => ⟪v i, A j⟫) * g A
      ∂Measure.pi (fun _ => stdGaussian E)) atTop
      (nhds ((∏ _j : Fin k, pairingsDensity v 0) * ∫⁻ R, g R ∂gaussianResidualRows v k)) := by
  simp_rw [constrained_gaussian_noise_integral hv k _ hg.measurable]
  apply constrained_gaussian_approximation_limit v k (matrixNormal m k)
    (fun n z j i => noiseScale n * z i j) (fun _ => by fun_prop) _ hg b hb hgb
  apply Filter.Eventually.of_forall
  intro z
  have h := (transposeCLE m k).continuous.tendsto 0 |>.comp (matrix_noise_shrinks z)
  convert h using 1 <;> rfl

lemma constrained_gaussian_noise_bound {m : ℕ} {v : Fin m → E}
    (hv : LinearIndependent ℝ v) (k n : ℕ) {g : (Fin k → E) → ℝ≥0∞} (hg : Measurable g)
    (b : ℝ≥0∞) (hgb : ∀ A, g A ≤ b) :
    (∫⁻ A, matrixNoiseDensity m k n (fun i j => ⟪v i, A j⟫) * g A
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (∏ _j : Fin k, pairingsDensity v 0) * b := by
  rw [constrained_gaussian_noise_integral hv k n hg]
  calc
    _ ≤ ∫⁻ z, ∫⁻ R, (∏ _j : Fin k, pairingsDensity v 0) * b
        ∂gaussianResidualRows v k ∂matrixNormal m k := by
      apply lintegral_mono
      intro z
      apply lintegral_mono
      intro R
      exact mul_le_mul' (Finset.prod_le_prod (fun j _ => pairingsDensity_le_zero _ _)) (hgb _)
    _ = _ := by simp

end Generic
end PosteriorReplicas
end

end OAI
