import OAI.Probability.SLE.Stochastic.PlanarHarmonicLocalization
import OAI.Probability.SLE.Geometry.ConformalLaplacian

namespace OAI

/-! The planar Brownian generator of a complex-plane harmonic function is
one half of its real Laplacian. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Complex InnerProductSpace
open scoped Topology NNReal ENNReal Laplacian

namespace SLEExactGauge

lemma second_derivative_constant_curve {u : ℂ → ℝ} {ψ : ℝ → ℂ} {a : ℝ} {v : ℂ}
    (hu : ContDiffAt ℝ 2 u (ψ a)) (hψ : ∀ r, HasDerivAt ψ v r) :
    iteratedDeriv 2 (fun r => u (ψ r)) a = fderiv ℝ (fderiv ℝ u) (ψ a) v v := by
  have hu1 : ContDiffAt ℝ 1 u (ψ a) := hu.of_le (by norm_num)
  have hevent : ∀ᶠ z in 𝓝 (ψ a), ContDiffAt ℝ 1 u z := hu1.eventually (by norm_num)
  have he : deriv (fun r => u (ψ r)) =ᶠ[𝓝 a] (fun r => fderiv ℝ u (ψ r) v) := by
    filter_upwards [(hψ a).continuousAt.tendsto.eventually hevent] with r hr
    exact ((hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r (hψ r)).deriv
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := (hd.comp_hasDerivAt a (hψ a)).clm_apply (hasDerivAt_const a v)
  have hv : deriv (fun r => fderiv ℝ u (ψ r) v) a=fderiv ℝ (fderiv ℝ u) (ψ a) v v := by
    simpa only [Function.comp_apply,map_zero,add_zero] using hc.deriv
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq,hv]

lemma planarGenerator_complex_eq (u : ℂ → ℝ) (z : ℝ×ℝ)
    (hu : ContDiffAt ℝ 2 u (Complex.equivRealProdCLM.symm z)) :
    planarGenerator (u ∘ Complex.equivRealProdCLM.symm) z=
      (1/2:ℝ)*(Δ u) (Complex.equivRealProdCLM.symm z) := by
  have hx : ∀ r : ℝ, HasDerivAt (fun x : ℝ => (x:ℂ)+(z.2:ℂ)*I) 1 r := by
    intro r
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := r)).add_const ((z.2:ℂ)*I)
  have hy : ∀ r : ℝ, HasDerivAt (fun y : ℝ => (z.1:ℂ)+(y:ℂ)*I) I r := by
    intro r
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
      ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const I).const_add (z.1:ℂ)
  have hu' : ContDiffAt ℝ 2 u ((z.1:ℂ)+(z.2:ℂ)*I) := by
    simpa only [Complex.equivRealProdCLM_symm_apply] using hu
  have hxr := second_derivative_constant_curve (ψ := fun x : ℝ => (x:ℂ)+(z.2:ℂ)*I)
    (a := z.1) hu' hx
  have hyr := second_derivative_constant_curve (ψ := fun y : ℝ => (z.1:ℂ)+(y:ℂ)*I)
    (a := z.2) hu' hy
  simp only [Function.comp_apply,Complex.equivRealProdCLM_symm_apply,planarGenerator]
  rw [hxr,hyr]
  congr 1
  simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
    Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]

lemma planarGenerator_harmonicAt (u : ℂ → ℝ) (z : ℝ×ℝ)
    (hu : HarmonicAt u (Complex.equivRealProdCLM.symm z)) :
    planarGenerator (u ∘ Complex.equivRealProdCLM.symm) z=0 := by
  rw [planarGenerator_complex_eq u z hu.1]
  simp only [hu.2.self_of_nhds,Pi.zero_apply,mul_zero]

end SLEExactGauge

end

end OAI
