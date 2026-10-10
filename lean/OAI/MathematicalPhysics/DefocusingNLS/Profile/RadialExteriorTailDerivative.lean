import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailRepresentation

namespace OAI

/-! The backward integral solves the weighted exterior differential equation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialExteriorPhase_hasDerivAt (t s : ℝ) :
    HasDerivAt (fun r => radialExteriorPhase r s)
      (-Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPhase t s) t := by
  simpa only [radialExteriorPropagator, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd', mul_one] using! (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t
      (radialExteriorPropagator_hasDerivAt t s (0,1))

theorem radialExteriorPropagator_curve_hasDerivAt (t s : ℝ)
    (v : ℝ → ℂ × ℂ) (v' : ℂ × ℂ) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun r => radialExteriorPropagator r s (v r))
      (v'.1, -Complex.I*(Real.exp (2*t)/2 : ℝ)*
        (radialExteriorPropagator t s (v t)).2 + radialExteriorPhase t s*v'.2) t := by
  have hfst : HasDerivAt (fun r => (v r).1) v'.1 t :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hv
  have hsnd : HasDerivAt (fun r => (v r).2) v'.2 t :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hv
  have h := hfst.prodMk ((radialExteriorPhase_hasDerivAt t s).mul hsnd)
  convert h using 1
  · rfl
  · apply Prod.ext
    · rfl
    · dsimp only [radialExteriorPropagator]
      ring

theorem radialExteriorTailIntegral_hasDerivAt (κ C t : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hbound : ∀ s, ‖g s‖ ≤ C) :
    HasDerivAt (radialExteriorTailIntegral κ g)
      (κ • radialExteriorTailIntegral κ g t +
        (0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(radialExteriorTailIntegral κ g t).2) + g t) t := by
  let H : ℝ → ℂ × ℂ := fun r => ∫ s in Ioi r, radialExteriorGauge κ g s
  have hH : HasDerivAt H (-radialExteriorGauge κ g t) t :=
    radial_tail_hasDerivAt (radialExteriorGauge κ g)
      (radialExteriorGauge_continuous κ g hg) (t-1) t (by linarith)
      (radialExteriorGauge_integrable κ C (t-1) hκ g hg hbound)
  have hP := radialExteriorPropagator_curve_hasDerivAt t 0 H _ hH
  have he : HasDerivAt (fun r : ℝ => -Real.exp (κ*r)) (-Real.exp (κ*t)*κ) t := by
    simpa [mul_comm] using! (((hasDerivAt_id t).const_mul κ).exp).neg
  have h := he.smul hP
  have heq : radialExteriorTailIntegral κ g =
      fun r => -Real.exp (κ*r) • radialExteriorPropagator r 0 (H r) := by
    funext r
    exact radialExteriorTailIntegral_representation κ C r hκ g hg hbound
  rw [heq]
  apply h.congr_deriv
  have hc : Real.exp (κ*t)*Real.exp (-(κ*t))=1 := by
    rw [← Real.exp_add]
    simp
  have hcancel : -Real.exp (κ*t) •
      radialExteriorPropagator t 0 (-radialExteriorGauge κ g t) = g t := by
    change -Real.exp (κ*t) •
      radialExteriorPropagatorMap t 0 (-radialExteriorGauge κ g t) = g t
    simp only [radialExteriorGauge,map_neg,map_smul,radialExteriorPropagatorMap_apply,
      radialExteriorPropagator_comp,radialExteriorPropagator_self,smul_neg,
      smul_smul,neg_mul,hc,neg_smul,one_smul,neg_neg]
  have hc1 := congrArg Prod.fst hcancel
  have hc2 := congrArg Prod.snd hcancel
  apply Prod.ext
  · simp only [Prod.fst_add,radialExteriorPropagator,Prod.smul_mk] at hc1 ⊢
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_neg] at hc1 ⊢
    linear_combination hc1
  · simp only [Prod.snd_add,radialExteriorPropagator,Prod.smul_mk] at hc2 ⊢
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_neg] at hc2 ⊢
    linear_combination hc2

end DefocusingNLS

end OAI
