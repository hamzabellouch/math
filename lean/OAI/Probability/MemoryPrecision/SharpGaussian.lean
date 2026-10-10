import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.AmbientGram

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression InnerProductSpace

def gaussianPeak : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹)

lemma sharp_gaussianReal_le_volume :
    gaussianReal 0 1 ≤ gaussianPeak • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  calc
    _ ≤ (volume : Measure ℝ).withDensity (fun _ => gaussianPeak) := by
      apply withDensity_mono
      filter_upwards [] with x
      apply ENNReal.ofReal_le_ofReal
      unfold gaussianPDFReal
      simp only [NNReal.coe_one, mul_one, sub_zero]
      exact mul_le_of_le_one_right (by positivity)
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg x)) (by positivity)))
    _ = _ := by rw [withDensity_const]

lemma sharp_pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤
      gaussianPeak ^ n • (volume : Measure (Fin n → ℝ)) := by
  have h := measure_pi_mono (fun _ : Fin n => sharp_gaussianReal_le_volume)
  rw [measure_pi_smul _ _ (show gaussianPeak ≠ ∞ from ENNReal.ofReal_ne_top)] at h
  simpa only [Fintype.card_fin, volume_pi] using h

section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance sharp_reference_sigmaFinite (m : ℕ) :
    SigmaFinite (matrixLabelReference (E := E) m) := by
  unfold matrixLabelReference
  infer_instance

lemma sharp_gaussian_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) ≤
      (gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) •
        (volume : Measure (Fin n → ℝ)) := by
  let u := gramSchmidtNormed ℝ v
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖) * gsUpper n v
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hv
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  have hexp (j : Fin n) : ∑ i, R i j • u i = v j := by
    rw [← gsUpper_expansion n v j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
    dsimp only [R]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal, gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  have hpos : 0 ≤ R.transpose.det := by rw [hdet]; positivity
  have hf : Measurable (Matrix.toLin' R.transpose) :=
    (Matrix.toLin' R.transpose).continuous_of_finiteDimensional.measurable
  have heq : (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' R.transpose) ∘ (fun x => fun i => ⟪u i, x⟫) := by
    funext x j
    rw [← hexp j]
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner,
      inner_smul_left]
  rw [heq, ← Measure.map_map hf (by fun_prop), orthonormal_gaussian_map hu]
  calc
    _ ≤ (gaussianPeak ^ n • (volume : Measure (Fin n → ℝ))).map
        (Matrix.toLin' R.transpose) :=
      Measure.map_mono (sharp_pi_gaussianReal_le_volume n) hf
    _ = _ := by
      rw [Measure.map_smul _ hf.aemeasurable, Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
        abs_of_nonneg (inv_nonneg.mpr hpos), hdet, smul_smul]

lemma sharp_gaussian_rows_pairings_le {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j i => ⟪v i, A j⟫) ≤
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
    (fun x : E => fun i => ⟪v i, x⟫)).aemeasurable)]
  have h := measure_pi_mono (fun _ : Fin m => sharp_gaussian_pairings_le v hv)
  rw [measure_pi_smul _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top
    (show gaussianPeak ≠ ∞ from ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top)] at h
  simpa only [Fintype.card_fin, volume_pi] using h
lemma sharp_gaussian_rows_kernel_bound {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m : ℕ) (y : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) ^ m) * ∏ j, φ (y j) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun z => ∏ j, φ (y j) * ∏ i, φ (y j - z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have heq (A : Fin m → E) :
      (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫) =
      H (fun j i => ⟪v i, A j⟫) := by
    dsimp [H]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (sharp_gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure]
      change _ * (∫⁻ z : Fin m → Fin n → ℝ, ∏ j, φ (y j) * ∏ i, φ (y j - z j i)) = _
      rw [lintegral_product_differences φ hφ hφ1]

lemma sharp_gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹)) ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - ⟪p, A j⟫)) *
        ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) (j : Fin m) :
        y j - ⟪p, A j⟫ - ⟪v i - p, A j⟫ = y j - ⟪v i, A j⟫ := by
      rw [inner_sub_left]
      ring
    simpa only [Pi.sub_apply, he] using
      lintegral_sub_right_eq_self
        (fun y : Fin m → ℝ => (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫))
        (fun j => ⟪p, A j⟫)
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : Fin m → ℝ,
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹)) ^ m) *
        ∏ j, φ (y j) := lintegral_mono fun y =>
          sharp_gaussian_rows_kernel_bound (fun i => v i - p) hv φ hφ hφ1 m y
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume m (fun _ => φ) (fun _ => hφ)]
      simp [hφ1]

lemma sharp_projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {H β R : ℝ} {z : E} (hH : 0 < H) (hR : 0 < R)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      ν (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ x, φ x = 1)
    {m : ℕ} (hm : 0 < m) (n : ℕ) (hgap : (n:ℝ)+(m:ℝ)-1 < β) :
    (∫⁻ Ay : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m Ay)^(n+1) ∂matrixLabelReference m) ≤
      gaussianPeak ^ (n*m) * ENNReal.ofReal
        (H^(n+1) * R^(β*(n+1:ℕ)-(m:ℝ)*(n:ℝ)) * ∏ j : Fin n, J β m j) := by
  simp_rw [projectionSmoothing_pow ν φ hφ m n]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ w : E × (Fin n → E), gaussianPeak ^ (n*m) * replicaWeight m w.1 w.2
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_joint_replica_independent hH hR hsupport hball hm n hgap] with w hw
      rw [matrixLabelReference, lintegral_prod _ (by fun_prop)]
      convert sharp_gaussian_replica_kernel_bound w.1 w.2 hw φ hφ hφ1 m using 1
      rw [mul_pow, ← pow_mul, replicaWeight_eq_det, sqrt_det_gram,
        ENNReal.ofReal_pow (by positivity)]
    _ = gaussianPeak ^ (n*m) *
        (∫⁻ w : E × (Fin n → E), replicaWeight m w.1 w.2
          ∂ν.prod (Measure.pi (fun _ => ν))) :=
      lintegral_const_mul _ (measurable_joint_replicaWeight m n)
    _ ≤ _ := mul_le_mul' le_rfl
      (joint_replica_integral_exact hH hR hsupport hball hm n hgap)

end Gaussian
end MemoryPrecision


end

end OAI
