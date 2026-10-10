import Mathlib
import OAI.Analysis.AffineBernstein.LogCaccioppoli

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SegmentEnergy

lemma matrix_dual_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v p : ι → ℝ) :
    (v ⬝ᵥ p)^2 ≤ (v ⬝ᵥ A.mulVec v) * inverseMatrixPair A p p := by
  have he : A⁻¹.mulVec (A.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.one_mulVec]
  have hc := inverseMatrixPair_cauchy hA (A.mulVec v) p
  rw [inverseMatrixPair_eq_dot, inverseMatrixPair_eq_dot,he] at hc
  simpa only [dotProduct_comm] using hc

lemma directional_derivative_sq_le {n : ℕ} {u f : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (v : Space n) :
    (dirDeriv v f x)^2 ≤ fderiv ℝ (fderiv ℝ u) x v v * inverseHessianPair u f f x := by
  have heQ : inverseHessianPair u f f x = inverseMatrixPair (hessian u x)
      (fun i => dirDeriv (coordinateVector n i) f x) (fun i => dirDeriv (coordinateVector n i) f x) := by
    unfold inverseHessianPair inverseMatrixPair
    rw [Finset.sum_comm]
    simp only [mul_right_comm]
  rw [dirDeriv_coordinate_sum,second_fderiv_eq_sum hu,heQ]
  convert matrix_dual_cauchy hp (fun i => v i) (fun i => dirDeriv (coordinateVector n i) f x) using 1 <;>
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

/-- Integral Cauchy--Schwarz with a pointwise dual pairing. No square roots or
strict positivity assumptions on the two nonnegative factors are required. -/
lemma integral_pair_cauchy {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {H E d : X → ℝ} (hH : Integrable H μ) (hE : Integrable E μ) (hd : Integrable d μ)
    (hHpos : ∀ x, 0 ≤ H x) (hEpos : ∀ x, 0 ≤ E x)
    (hpair : ∀ x, (d x)^2 ≤ H x * E x) :
    (∫ x, d x ∂μ)^2 ≤ (∫ x, H x ∂μ)*(∫ x, E x ∂μ) := by
  have hquad (a : ℝ) : 0 ≤ (∫ x, H x ∂μ)*(a*a) +
      (2*∫ x, d x ∂μ)*a + ∫ x, E x ∂μ := by
    have hp (x : X) : 0 ≤ a^2*H x+(2*a)*d x+E x := by
      have hh := paired_cauchy_coercive (hHpos x) (hEpos x) (hpair x)
        (sq_nonneg a) zero_lt_one (show (2*a)^2 ≤ 4*a^2*1 by nlinarith)
      simpa only [one_mul] using hh
    have hi := MeasureTheory.integral_nonneg (μ := μ) (show 0 ≤ (fun x => a^2*H x+(2*a)*d x+E x) from hp)
    rw [integral_add (f := fun x => a^2*H x+(2*a)*d x) (g := E)
      ((hH.const_mul (a^2)).add (hd.const_mul (2*a))) hE,
      integral_add (f := fun x => a^2*H x) (g := fun x => (2*a)*d x)
      (hH.const_mul (a^2)) (hd.const_mul (2*a)),integral_const_mul,integral_const_mul] at hi
    nlinarith
  have hh := discrim_le_zero hquad
  unfold discrim at hh
  nlinarith

lemma segment_energy_bound {n : ℕ} {u f : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x, (hessian u x).PosDef) (x y : Space n) :
    (f y-f x)^2 ≤ ((fderiv ℝ u y-fderiv ℝ u x) (y-x)) *
      ∫ t in (0:ℝ)..1, inverseHessianPair u f f (x+t • (y-x)) := by
  let v := y-x
  let α : ℝ → Space n := fun t => x+t • v
  have hα : ContDiff ℝ ∞ α := contDiff_const.add (contDiff_id.smul contDiff_const)
  let H : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (α t) v v
  let E : ℝ → ℝ := fun t => inverseHessianPair u f f (α t)
  let d : ℝ → ℝ := fun t => dirDeriv v f (α t)
  have hHc : Continuous H :=
    (((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous.comp
      hα.continuous).clm_apply continuous_const |>.clm_apply continuous_const
  have hEc : Continuous E := (contDiff_inverseHessianPair_global hu hp hf hf).continuous.comp hα.continuous
  have hdc : Continuous d := (contDiff_dirDeriv hf v).continuous.comp hα.continuous
  have hh := integral_pair_cauchy (μ := volume.restrict (Icc (0:ℝ) 1)) (hHc.integrableOn_Icc) (hEc.integrableOn_Icc) (hdc.integrableOn_Icc)
    (fun t => second_fderiv_nonneg hu.contDiffAt (hp (α t)).posSemidef v)
    (fun t => inverseHessianPair_self_nonneg (hp (α t)) f)
    (fun t => directional_derivative_sq_le hu.contDiffAt (hp (α t)) v)
  have hdi : (∫ t in (0:ℝ)..1, d t) = f y-f x := by
    have hd' (t : ℝ) : HasDerivAt (fun t => f (α t)) (d t) t := by
      apply HasDerivAt.congr_deriv ((hf.differentiable (by simp) (α t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)))
      simp only [zero_add,one_smul]
      rfl
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun parameter _ => hd' parameter) (hdc.intervalIntegrable 0 1)
    simpa only [α,v,zero_smul,add_zero,one_smul,add_sub_cancel] using hi
  have hHi : (∫ t in (0:ℝ)..1, H t) = (fderiv ℝ u y-fderiv ℝ u x) v := by
    let q := fun z => fderiv ℝ u z v
    have hq : ContDiff ℝ ∞ q := (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdq (z : Space n) : dirDeriv v q z = fderiv ℝ (fderiv ℝ u) z v v := by
      unfold dirDeriv q
      rw [((((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z).hasFDerivAt).clm_apply
        (hasFDerivAt_const v z)).fderiv]
      simp
    have hd' (t : ℝ) : HasDerivAt (fun t => q (α t)) (H t) t := by
      have hdt := ((hq.differentiable (by simp) (α t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)))
      apply hdt.congr_deriv
      simp only [one_smul,zero_add]
      exact hdq (α t)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun parameter _ => hd' parameter) (hHc.intervalIntegrable 0 1)
    simpa only [α,q,v,zero_smul,add_zero,one_smul,add_sub_cancel,sub_apply] using hi
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))] at hdi hHi ⊢
  rw [← hdi,← hHi]
  exact hh

end SegmentEnergy




end
end AffineBernstein
end

end OAI
