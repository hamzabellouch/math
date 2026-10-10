import Mathlib
import OAI.Probability.SKBarriers.Scalar.GrowthOperations

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem HasExpGrowth.integrable_tilted_fiberGaussian {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (V : ParameterSpace n → ℝ) (hV : BoundedDerivs V)
    {g : ParameterSpace n → F} (hg : HasExpGrowth g) (hc : Continuous g) (x : ℝ) :
    Integrable g ((fiberGaussian n x).tilted V) := by
  have he : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  have hce := Real.continuous_exp.comp hV.1.continuous
  rw [integrable_tilted_iff (he.integrable_fiberGaussian n hce x)]
  exact (he.smul hg).integrable_fiberGaussian n (hce.smul hc) x

theorem HasExpGrowth.memLp_two_tilted_fiberGaussian (n : ℕ)
    (V : ParameterSpace n → ℝ) (hV : BoundedDerivs V) {g : ParameterSpace n → ℝ}
    (hg : HasExpGrowth g) (hc : Continuous g) (x : ℝ) :
    MemLp g 2 ((fiberGaussian n x).tilted V) := by
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  simpa only [pow_two] using (hg.mul hg).integrable_tilted_fiberGaussian n V hV (hc.mul hc) x

theorem fiberGaussian_tilted_probability (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) : IsProbabilityMeasure ((fiberGaussian n x).tilted V) := by
  apply isProbabilityMeasure_tilted
  have he : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  exact he.integrable_fiberGaussian n (Real.continuous_exp.comp hV.1.continuous) x

section Directional
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def directionalGradient (F : E → ℝ) (u : E) (z : E) : ℝ := fderiv ℝ F z u

theorem directionalGradient_contDiff (F : E → ℝ) (hF : ContDiff ℝ 2 F) (u : E) :
    ContDiff ℝ 1 (directionalGradient F u) :=
  (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem fderiv_directionalGradient (F : E → ℝ) (hF : ContDiff ℝ 2 F) (u z : E) :
    fderiv ℝ (directionalGradient F u) z = (fderiv ℝ (fderiv ℝ F) z).flip u := by
  have H := (((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt.clm_apply
    (hasFDerivAt_const u z)).fderiv
  change fderiv ℝ (fun y => fderiv ℝ F y u) z = _
  simpa only [ContinuousLinearMap.comp_zero,zero_add] using H

theorem BoundedDerivs.directionalGradient_bounds {F : E → ℝ} (hF : BoundedDerivs F) (u : E) :
    HasExpGrowth (directionalGradient F u) ∧ HasExpGrowth (fderiv ℝ (directionalGradient F u)) := by
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hF
  constructor
  · exact (HasExpGrowth.of_bounded hC hb).derivative_eval u
  · apply HasExpGrowth.of_bounded (mul_nonneg hD (norm_nonneg u))
    intro z
    rw [fderiv_directionalGradient F hc]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hD (norm_nonneg u))
    intro v
    calc
      ‖(fderiv ℝ (fderiv ℝ F) z).flip u v‖ ≤
          ‖fderiv ℝ (fderiv ℝ F) z v‖*‖u‖ := (fderiv ℝ (fderiv ℝ F) z v).le_opNorm u
      _ ≤ (D*‖v‖)*‖u‖ := mul_le_mul_of_nonneg_right
          (((fderiv ℝ (fderiv ℝ F) z).le_opNorm v).trans
            (mul_le_mul_of_nonneg_right (hbb z) (norm_nonneg v))) (norm_nonneg u)
      _ = _ := by ring
end Directional

def gaussianResponse (n : ℕ) (F : ParameterSpace n → ℝ) (p x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i)
    ∂(fiberGaussian n x).tilted (fun z => p*F z)) +
    p*cov[directionalGradient F (coordinateAxis n i),directionalGradient F (coordinateAxis n j);
      (fiberGaussian n x).tilted (fun z => p*F z)]

theorem gaussian_tilted_coordinate_mean (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (i : Fin n) :
    (∫ z, coordinateProjection n i z ∂(fiberGaussian n x).tilted (fun z => p*F z)) =
      p*∫ z, directionalGradient F (coordinateAxis n i) z
        ∂(fiberGaussian n x).tilted (fun z => p*F z) := by
  rw [fiberGaussian_tilted_stein n _ (hF.const_mul p)]
  simp_rw [((hF.1.differentiable (by norm_num) _).hasFDerivAt.const_mul p).fderiv,
    smul_apply,smul_eq_mul]
  exact integral_const_mul _ _

theorem gaussian_tilted_cross_covariance (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (i j : Fin n) :
    cov[directionalGradient F (coordinateAxis n i),coordinateProjection n j;
      (fiberGaussian n x).tilted (fun z => p*F z)] = gaussianResponse n F p x i j := by
  let μ := (fiberGaussian n x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability n _ (hF.const_mul p) x
  have hg := directionalGradient_contDiff F hF.1 (coordinateAxis n i)
  obtain ⟨hg₀,hg₁⟩ := hF.directionalGradient_bounds (coordinateAxis n i)
  have hm (i : Fin n) : MemLp (directionalGradient F (coordinateAxis n i)) 2 μ :=
    (hF.directionalGradient_bounds _).1.memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (directionalGradient_contDiff F hF.1 _).continuous x
  have hy (j : Fin n) : MemLp (coordinateProjection n j) 2 μ :=
    (HasExpGrowth.linear _).memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (coordinateProjection n j).continuous x
  have H := fiberGaussian_tilted_weighted_stein n (fun z => p*F z)
    (directionalGradient F (coordinateAxis n i)) (hF.const_mul p) hg hg₀ hg₁ x j
  simp_rw [fderiv_directionalGradient F hF.1,
    ((hF.1.differentiable (by norm_num) _).hasFDerivAt.const_mul p).fderiv,
    ContinuousLinearMap.flip_apply,smul_apply,smul_eq_mul] at H
  have hmj := gaussian_tilted_coordinate_mean n F hF p x j
  change (∫ z, coordinateProjection n j z ∂μ) = _ at hmj
  change (∫ z, coordinateProjection n j z*directionalGradient F (coordinateAxis n i) z ∂μ) = _ at H
  rw [covariance_eq_sub (hm i) (hy j)]
  unfold gaussianResponse
  rw [covariance_eq_sub (hm i) (hm j)]
  simp only [Pi.mul_apply]
  change _ = (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i) ∂μ)+_
  have he : (∫ z, directionalGradient F (coordinateAxis n i) z*
      (p*fderiv ℝ F z (coordinateAxis n j)) ∂μ) =
      p*∫ z, directionalGradient F (coordinateAxis n i) z*
        directionalGradient F (coordinateAxis n j) z ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext z
    unfold directionalGradient
    ring
  rw [he] at H
  have he₂ : (∫ z, directionalGradient F (coordinateAxis n i) z*coordinateProjection n j z ∂μ) =
      ∫ z, coordinateProjection n j z*directionalGradient F (coordinateAxis n i) z ∂μ := by
    congr 1; funext z; ring
  rw [he₂,H,hmj]
  ring

@[simp]
theorem coordinateProjection_coordinateAxis (n : ℕ) (i j : Fin n) :
    coordinateProjection n i (coordinateAxis n j) = if i=j then 1 else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [coordinateProjection,coordinateAxis]
      · simp [coordinateProjection,coordinateAxis,(Fin.castSucc_ne_last j).symm]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [coordinateProjection,coordinateAxis]
      · simpa [coordinateProjection,coordinateAxis] using ih i j

theorem gaussianResponse_isHermitian (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : ContDiff ℝ 2 F) (p x : ℝ) : (gaussianResponse n F p x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,gaussianResponse]
  rw [covariance_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  exact (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

theorem gaussian_tilted_field_covariance (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (i j : Fin n) :
    cov[coordinateProjection n i,coordinateProjection n j;
      (fiberGaussian n x).tilted (fun z => p*F z)] =
      (if i=j then 1 else 0)+p*gaussianResponse n F p x i j := by
  let μ := (fiberGaussian n x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability n _ (hF.const_mul p) x
  have hm (i : Fin n) : MemLp (directionalGradient F (coordinateAxis n i)) 2 μ :=
    (hF.directionalGradient_bounds _).1.memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (directionalGradient_contDiff F hF.1 _).continuous x
  have hy (j : Fin n) : MemLp (coordinateProjection n j) 2 μ :=
    (HasExpGrowth.linear _).memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
      (coordinateProjection n j).continuous x
  have hg' : HasExpGrowth (fderiv ℝ (fun z => coordinateProjection n i z)) := by
    have he : fderiv ℝ (fun z => coordinateProjection n i z) = fun _ => coordinateProjection n i := by
      funext z; exact (coordinateProjection n i).fderiv
    rw [he]
    exact HasExpGrowth.of_bounded (norm_nonneg _) (fun _ => le_rfl)
  have H := fiberGaussian_tilted_weighted_stein n (fun z => p*F z)
    (coordinateProjection n i) (hF.const_mul p) (coordinateProjection n i).contDiff
    (HasExpGrowth.linear _) hg' x j
  simp_rw [(coordinateProjection n i).fderiv,
    ((hF.1.differentiable (by norm_num) _).hasFDerivAt.const_mul p).fderiv,
    smul_apply,smul_eq_mul,coordinateProjection_coordinateAxis] at H
  change (∫ z, coordinateProjection n j z*coordinateProjection n i z ∂μ) =
    (∫ _, (if i=j then 1 else 0 : ℝ) ∂μ)+
      ∫ z, coordinateProjection n i z*(p*fderiv ℝ F z (coordinateAxis n j)) ∂μ at H
  simp only [integral_const,probReal_univ,one_smul] at H
  have he : (∫ z, coordinateProjection n i z*(p*fderiv ℝ F z (coordinateAxis n j)) ∂μ) =
      p*∫ z, directionalGradient F (coordinateAxis n j) z*coordinateProjection n i z ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext z; unfold directionalGradient; ring
  rw [he] at H
  have hr := gaussian_tilted_cross_covariance n F hF p x j i
  change cov[directionalGradient F (coordinateAxis n j),coordinateProjection n i;μ] = _ at hr
  rw [covariance_eq_sub (hm j) (hy i)] at hr
  have hs : gaussianResponse n F p x j i = gaussianResponse n F p x i j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
      (gaussianResponse_isHermitian n F hF.1 p x).eq
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  rw [hs] at hr
  rw [covariance_eq_sub (hy i) (hy j)]
  simp only [Pi.mul_apply] at hr ⊢
  have hc : (∫ z, coordinateProjection n i z*coordinateProjection n j z ∂μ) =
      ∫ z, coordinateProjection n j z*coordinateProjection n i z ∂μ := by
    congr 1; funext z; ring
  rw [hc,H]
  have hj := gaussian_tilted_coordinate_mean n F hF p x j
  change (∫ z, coordinateProjection n j z ∂μ) = _ at hj
  rw [hj,← hr]
  ring

end SK.Analytic

end
end
end
end
end
end
end

end OAI
