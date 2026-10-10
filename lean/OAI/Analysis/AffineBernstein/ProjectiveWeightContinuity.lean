import Mathlib
import OAI.Analysis.AffineBernstein.MatrixMetric
import OAI.Analysis.AffineBernstein.TubeInvariantSmooth

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ProjectiveWeightContinuity
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma continuousAt_supportConormal {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) : ContinuousAt (supportConormal H) q := by
  have hd := (hH.fderiv_right (m := ∞) (by simp)).continuousAt
  change ContinuousAt (fun y => (fderiv ℝ H y).comp _ -
    (InnerProductSpace.toDual ℝ E y.2).comp _) q
  exact (hd.clm_comp continuousAt_const).sub
    (((InnerProductSpace.toDual ℝ E).continuous.continuousAt.comp continuousAt_snd).clm_comp
      continuousAt_const)

lemma continuousAt_inverseMatrixPair {X : Type*} [TopologicalSpace X]
    {A : X → Matrix ι ι ℝ} {x : X} (hA : ContinuousAt A x) (hd : (A x).det ≠ 0)
    (v w : ι → ℝ) : ContinuousAt (fun y => inverseMatrixPair (A y) v w) x := by
  have hi : ContinuousAt (fun y => (A y)⁻¹) x :=
    (continuousAt_matrix_inv (A x) (by simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ hd))).comp hA
  unfold inverseMatrixPair
  have hij (i j : ι) : ContinuousAt (fun y => (A y)⁻¹ i j) x := (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hi)
  fun_prop

lemma continuousAt_sphericalInverseArea {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ)
    (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE)
    (v w : ι → ℝ) :
    ContinuousAt (fun y => (Real.rpow (tubeBaseMatrix H y bS).det δ *
        Real.rpow (tubeAngularDensity H y bE) (1-δ)) *
      (‖supportConormal H y‖ * inverseMatrixPair (tubeBaseMatrix H y bS) v w)) q := by
  have hb := (contDiffAt_tubeBaseMatrix hH bS).continuousAt
  have hq := (contDiffAt_tubeAngularDensity hH bE).continuousAt
  have hd := continuous_id.matrix_det.continuousAt.comp hb
  have hν : ContinuousAt (fun y => ‖supportConormal H y‖) q :=
    (@continuous_norm ((S × E) →L[ℝ] ℝ) inferInstance).continuousAt.comp
      (continuousAt_supportConormal hH)
  exact ((hd.rpow_const (Or.inl hB.ne')).mul (hq.rpow_const (Or.inl hQ.ne'))).mul
    (hν.mul
      (continuousAt_inverseMatrixPair hb hB.ne' v w))

end ProjectiveWeightContinuity

open intervalIntegral

lemma lintegral_smul_jacobian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : F → ℝ≥0∞)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t^Module.finrank ℝ F) * (∫⁻ x, f (t • x) ∂μ) = ∫⁻ x, f x ∂μ := by
  have hm := lintegral_map_equiv (μ := μ) f
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr ht.ne').unit).toMeasurableEquiv
  change (∫⁻ x, f x ∂Measure.map (fun x : F => t • x) μ) = ∫⁻ x, f (t • x) ∂μ at hm
  rw [Measure.map_addHaar_smul μ ht.ne',lintegral_smul_measure] at hm
  rw [← hm,smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg ht.le _)]
  rw [abs_of_pos (inv_pos.mpr (pow_pos ht _)),mul_inv_cancel₀ (pow_pos ht _).ne']
  simp

lemma projective_norm_pos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : F) : 0 < ‖WithLp.toLp 2 (x,(1:ℝ))‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hh := congrArg (fun q : WithLp 2 (F × ℝ) => (WithLp.ofLp q).2) h
  simp at hh

/- Exact radial slice integral, retaining the dimension-zero tangent endpoint. -/
lemma lintegral_pow_Ioo {k : ℕ} {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioo 0 r, ENNReal.ofReal (t^k)) = ENNReal.ofReal (r^(k+1)/(k+1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow k).1]
  · rw [← intervalIntegral.integral_of_le hr.le]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le _

end AffineBernstein
end

end OAI
