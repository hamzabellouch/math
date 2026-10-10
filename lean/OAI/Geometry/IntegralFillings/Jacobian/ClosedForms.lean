import Mathlib
import OAI.Geometry.IntegralFillings.Currents.Basic

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal

namespace SharpIntegralFillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma integral_fderiv_compact_eq_zero {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (v : E) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hI : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hfc
  have hD : Integrable (fun x => fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ v)
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : E => (1 : ℝ)) (g := f) (v := v) (μ := μ)
    (by simp) (by simpa using hD) (by simpa using hI)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => hf.differentiable (by norm_num) x)
  simpa using H

lemma integral_extDeriv_compact_eq_zero {n : ℕ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} (hω : ContDiff ℝ 1 ω)
    (hωc : HasCompactSupport ω) (v : Fin (n+1) → E) :
    (∫ x, extDeriv ω x v ∂μ) = 0 := by
  have hs (i : Fin (n+1)) : ContDiff ℝ 1 (fun x => ω x (i.removeNth v)) :=
    (ContinuousAlternatingMap.apply ℝ E ℝ (i.removeNth v)).contDiff.comp hω
  have hc (i : Fin (n+1)) : HasCompactSupport (fun x => ω x (i.removeNth v)) :=
    hωc.comp_left (g := fun a : E [⋀^Fin n]→L[ℝ] ℝ => a (i.removeNth v)) (by simp)
  have hI (i : Fin (n+1)) : Integrable
      (fun x => (-1 : ℝ)^i.val * fderiv ℝ (fun y => ω y (i.removeNth v)) x (v i)) μ := by
    apply Integrable.const_mul
    exact (((hs i).continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hc i).fderiv_apply ℝ (v i))
  simp_rw [extDeriv_apply (hω.differentiable one_ne_zero _)]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp only [integral_const_mul, integral_fderiv_compact_eq_zero μ (hs _) (hc _),mul_zero,
    Finset.sum_const_zero]

lemma integral_extDeriv_scalar_eq_zero {n : ℕ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} (hω : Differentiable ℝ ω)
    (hωc : HasCompactSupport ω)
    (hs : ∀ w : Fin n → E, ContDiff ℝ 1 (fun x => ω x w))
    (v : Fin (n+1) → E) : (∫ x, extDeriv ω x v ∂μ) = 0 := by
  have hc (i : Fin (n+1)) : HasCompactSupport (fun x => ω x (i.removeNth v)) :=
    hωc.comp_left (g := fun a : E [⋀^Fin n]→L[ℝ] ℝ => a (i.removeNth v)) (by simp)
  have hI (i : Fin (n+1)) : Integrable
      (fun x => (-1 : ℝ)^i.val * fderiv ℝ (fun y => ω y (i.removeNth v)) x (v i)) μ := by
    apply Integrable.const_mul
    exact (((hs _).continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hc i).fderiv_apply ℝ (v i))
  simp_rw [extDeriv_apply (hω _)]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp only [integral_const_mul, integral_fderiv_compact_eq_zero μ (hs _) (hc _), mul_zero,
    Finset.sum_const_zero]

noncomputable def rowVolume (n : ℕ) : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

lemma rowVolume_apply {n : ℕ} (w : Fin n → (Fin n → ℝ)) :
    rowVolume n w = Matrix.det w := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma extDeriv_mul_form {n : ℕ} {f : E → ℝ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hω : DifferentiableAt ℝ ω x)
    (v : Fin (n+1) → E) :
    extDeriv (fun z => f z • ω z) x v =
      f x * extDeriv ω x v +
        ∑ i, (-1 : ℝ)^i.val * fderiv ℝ f x (v i) * ω x (i.removeNth v) := by
  rw [extDeriv, fderiv_fun_smul hf hω,
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma closed_pullback_rowVolume {n : ℕ} {g : E → Fin n → ℝ}
    (hg : ContDiff ℝ 2 g) (x : E) :
    extDeriv (fun z => (rowVolume n).compContinuousLinearMap (fderiv ℝ g z)) x = 0 := by
  have H := extDeriv_pullback (ω := fun _ : Fin n → ℝ => rowVolume n)
    (f := g) (x := x) (differentiableAt_const _) hg.contDiffAt
    (by simp : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  rw [H]
  ext v
  simp [extDeriv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]

lemma integral_smooth_jacobian_eq_zero {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (v : Fin (n+1) → E) :
    (∫ x, Matrix.det (Matrix.of (fun i =>
      Matrix.vecCons (fderiv ℝ f x (v i)) (fderiv ℝ g x (v i)))) ∂μ) = 0 := by
  let α : E → E [⋀^Fin n]→L[ℝ] ℝ :=
    fun x => (rowVolume n).compContinuousLinearMap (fderiv ℝ g x)
  have hg' : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hα (x : E) : DifferentiableAt ℝ α x :=
    (differentiableAt_const _).continuousAlternatingMapCompContinuousLinearMap
      (hg'.differentiable one_ne_zero x)
  have hs (w : Fin n → E) : ContDiff ℝ 1 (fun x => α x w) := by
    exact (rowVolume n).toContinuousMultilinearMap.contDiff.comp
      (contDiff_pi.mpr (fun i => hg'.clm_apply contDiff_const))
  have hω : Differentiable ℝ (fun x => f x • α x) :=
    fun x => (hf.differentiable one_ne_zero x).smul (hα x)
  have H := integral_extDeriv_scalar_eq_zero μ hω hfc.smul_right
    (fun w => by simpa using hf.mul (hs w)) v
  convert H using 1
  apply integral_congr_ae
  filter_upwards with x
  rw [extDeriv_mul_form (hf.differentiable one_ne_zero x) (hα x)]
  change _ = f x * extDeriv (fun z => (rowVolume n).compContinuousLinearMap
    (fderiv ℝ g z)) x v + _
  rw [closed_pullback_rowVolume hg x]
  simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero, zero_add]
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.of_apply, Matrix.cons_val_zero, α,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, rowVolume_apply]
  congr 2

end SharpIntegralFillings
end

end OAI
