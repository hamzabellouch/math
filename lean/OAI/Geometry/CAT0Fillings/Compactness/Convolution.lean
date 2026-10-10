import Mathlib

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution Pointwise

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma convolution_scalar_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f ρ : E → ℝ} (hf : Integrable f μ) {C M : ℝ}
    (hC : 0 ≤ C) (hρ : ∀ x, |ρ x| ≤ C) (hM : (∫ x, |f x| ∂μ) ≤ M) (x : E) :
    |(f ⋆[lsmul ℝ ℝ, μ] ρ) x| ≤ C*M := by
  rw [convolution_def]
  have hb := norm_integral_le_of_norm_le (hf.abs.mul_const C)
    (ae_of_all μ fun y => show ‖(lsmul ℝ ℝ (f y)) (ρ (x-y))‖ ≤ |f y| *C by
      simpa only [lsmul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul] using
        mul_le_mul_of_nonneg_left (hρ (x-y)) (abs_nonneg (f y)))
  rw [integral_mul_const] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hM hC).trans_eq (mul_comm _ _))

lemma convolution_scalar_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f ρ : E → ℝ} (hf : Integrable f μ)
    (hρc : HasCompactSupport ρ) {K M : ℝ≥0} (hρ : LipschitzWith K ρ)
    (hM : (∫ x, |f x| ∂μ) ≤ M) :
    LipschitzWith (K*M) (f ⋆[lsmul ℝ ℝ, μ] ρ) := by
  have hi (x : E) : Integrable (fun y => f y*ρ (x-y)) μ :=
    hρc.convolutionExists_right (lsmul ℝ ℝ) hf.locallyIntegrable hρ.continuous x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,convolution_def,lsmul_apply,smul_eq_mul]
  rw [←integral_sub (hi x) (hi y)]
  have hh := norm_integral_le_of_norm_le (hf.abs.mul_const ((K:ℝ)*dist x y))
    (ae_of_all μ fun z => show ‖f z*ρ (x-z)-f z*ρ (y-z)‖ ≤ |f z| *((K:ℝ)*dist x y) by
      rw [←mul_sub,Real.norm_eq_abs,abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.dist_eq,dist_sub_right] using hρ.dist_le_mul (x-z) (y-z))
  rw [integral_mul_const] at hh
  apply hh.trans
  calc (∫ z, |f z| ∂μ)*((K:ℝ)*dist x y) ≤ (M:ℝ)*((K:ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_right hM (mul_nonneg K.coe_nonneg dist_nonneg)
    _ = ((K*M:ℝ≥0):ℝ)*dist x y := by push_cast; ring

lemma convolution_scalar_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f ρ : E → ℝ} {R ε : ℝ}
    (hf : Function.support f ⊆ closedBall (0:E) R)
    (hρ : Function.support ρ ⊆ closedBall (0:E) ε) :
    Function.support (f ⋆[lsmul ℝ ℝ, μ] ρ) ⊆ closedBall (0:E) (R+ε) := by
  intro x hx
  obtain ⟨y,hy,z,hz,rfl⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hx
  have hy' : ‖y‖ ≤ ε := by simpa only [mem_closedBall,dist_zero_right] using hρ hy
  have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hf hz
  simp only [mem_closedBall,dist_zero_right]
  exact (norm_add_le y z).trans ((add_le_add hy' hz').trans_eq (add_comm _ _))

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ENNReal NNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma mollifier_error_of_translation {f : E → ℝ} (hf : Integrable f μ)
    {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ w, (∫ x, |f (x+w)-f x| ∂μ) ≤ C*‖w‖) (η : ContDiffBump (0:E)) :
    (∫ x, |f x-(η.normed μ ⋆[lsmul ℝ ℝ, μ] f) x| ∂μ) ≤ C*η.rOut := by
  let ρ := η.normed μ
  have hρ : Integrable ρ μ := η.continuous_normed.integrable_of_hasCompactSupport η.hasCompactSupport_normed
  have hρ0 : ∀ x, 0 ≤ ρ x := η.nonneg_normed
  have hfi : Integrable (ρ ⋆[lsmul ℝ ℝ, μ] f) μ := hρ.integrable_convolution (lsmul ℝ ℝ) hf
  have hconv (x : E) : Integrable (fun y => ρ y*f (x-y)) μ := by
    exact (η.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      η.continuous_normed hf.locallyIntegrable x)
  have hp : Integrable (fun p : E × E => ρ p.2*(f p.1-f (p.1-p.2))) (μ.prod μ) := by
    have h1 := (hf.mul_prod hρ)
    have h2 := hρ.convolution_integrand (lsmul ℝ ℝ) hf
    convert h1.sub h2 using 1
    funext p
    simp only [Pi.sub_apply,lsmul_apply,smul_eq_mul]
    ring
  have hpoint (x : E) : |f x-(ρ ⋆[lsmul ℝ ℝ, μ] f) x| ≤
      ∫ y, ρ y*|f x-f (x-y)| ∂μ := by
    have he : f x-(ρ ⋆[lsmul ℝ ℝ, μ] f) x = ∫ y, ρ y*(f x-f (x-y)) ∂μ := by
      simp only [mul_sub]
      rw [integral_sub (hρ.mul_const _) (hconv x),integral_mul_const]
      simp only [ρ,η.integral_normed,one_mul,convolution_def,lsmul_apply,smul_eq_mul]
    rw [he]
    have hn := norm_integral_le_integral_norm (f := fun y => ρ y*(f x-f (x-y))) (μ := μ)
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hρ0 _)] using hn
  have hpn : Integrable (fun p : E × E => ρ p.2*|f p.1-f (p.1-p.2)|) (μ.prod μ) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hρ0 _)] using hp.abs
  have hh := integral_mono (hf.sub hfi).abs hpn.integral_prod_left hpoint
  rw [integral_integral_swap hpn] at hh
  have hb (y : E) : (∫ x, ρ y*|f x-f (x-y)| ∂μ) ≤ ρ y*(C*η.rOut) := by
    rw [integral_const_mul]
    by_cases hy : y ∈ Function.support ρ
    · have hyn : ‖y‖ ≤ η.rOut := by
        have hys : Function.support ρ ⊆ closedBall 0 η.rOut := by
          dsimp [ρ]
          rw [η.support_normed_eq]
          exact ball_subset_closedBall
        simpa only [mem_closedBall,dist_zero_right] using hys hy
      have ht' : (∫ x, |f x-f (x-y)| ∂μ) ≤ C*‖y‖ := by
        simpa only [←sub_eq_add_neg,norm_neg,abs_sub_comm] using ht (-y)
      exact mul_le_mul_of_nonneg_left (ht'.trans (mul_le_mul_of_nonneg_left hyn hC)) (hρ0 y)
    · have hz : ρ y = 0 := Function.notMem_support.mp hy
      simp only [hz,zero_mul,le_refl]
  have hm := integral_mono hpn.integral_prod_right (hρ.mul_const (C*η.rOut)) hb
  rw [integral_mul_const] at hm
  have hr : (∫ y, ρ y ∂μ) = 1 := η.integral_normed
  rw [hr,one_mul] at hm
  exact hh.trans hm

end CAT0Fillings.JointBV
end

end OAI
