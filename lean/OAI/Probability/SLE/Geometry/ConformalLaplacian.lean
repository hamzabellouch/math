import OAI.Probability.SLE.RadiusClocks
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

namespace OAI

/-! The real Laplacian transforms by the squared complex derivative.
This is the change-of-variables identity used for the exterior area proof. -/
noncomputable section
open Set Filter Metric Function Complex InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma complex_composition_hessian {f : ℂ → ℂ} {u : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hu : ContDiffAt ℝ 2 u (f z)) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (u ∘ f)) z v v =
      fderiv ℝ (fderiv ℝ u) (f z) (fderiv ℝ f z v) (fderiv ℝ f z v)+
      fderiv ℝ u (f z) (fderiv ℝ (fderiv ℝ f) z v v) := by
  have hf1 : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) z := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu2 : DifferentiableAt ℝ (fderiv ℝ u) (f z) := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc := (hu2.hasFDerivAt.comp z hf1.hasFDerivAt).clm_comp hf2.hasFDerivAt
  have he : fderiv ℝ (u ∘ f) =ᶠ[𝓝 z]
      (fun a => (fderiv ℝ u (f a)).comp (fderiv ℝ f a)) := by
    filter_upwards [hf.eventually (by norm_num),
      hf1.continuousAt.tendsto.eventually (hu.eventually (by norm_num))] with a hfa hua
    exact fderiv_comp a (hua.differentiableAt (by norm_num)) (hfa.differentiableAt (by norm_num))
  have hd := hc.congr_of_eventuallyEq he
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,Function.comp_apply]
  ring

lemma complex_fderiv_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (v : ℂ) :
    fderiv ℝ f z v=v*deriv f z := by
  rw [hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ |>.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]

lemma laplacian_holomorphic_comp {f : ℂ → ℂ} {u : ℂ → ℝ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hu : ContDiffAt ℝ 2 u (f z)) :
    (Δ (u ∘ f)) z=‖deriv f z‖^2*(Δ u) (f z) := by
  have hfR : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  have he0 : fderiv ℝ (fderiv ℝ f) z 1 1+fderiv ℝ (fderiv ℝ f) z I I=0 := by
    have hh := hf.harmonicAt.2.self_of_nhds
    simpa only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
      Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Pi.zero_apply] using hh
  have hh := complex_hessian_rotation (u := u) (f z) (deriv f z)
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [complex_composition_hessian hfR hu 1,complex_composition_hessian hfR hu I,
    complex_fderiv_apply hf.differentiableAt,complex_fderiv_apply hf.differentiableAt,one_mul]
  calc
    _ = (fderiv ℝ (fderiv ℝ u) (f z) (deriv f z) (deriv f z)+
        fderiv ℝ (fderiv ℝ u) (f z) (deriv f z*I) (deriv f z*I))+
        fderiv ℝ u (f z) (fderiv ℝ (fderiv ℝ f) z 1 1+fderiv ℝ (fderiv ℝ f) z I I) := by
      rw [map_add]
      simp only [mul_comm I]
      ring
    _ = _ := by rw [he0,map_zero,add_zero,hh]

end SLEExactGauge

end

end OAI
