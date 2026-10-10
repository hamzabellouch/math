import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreFreeIntegral

namespace OAI

/-! Exact Wronskian transport for the free radial matching equation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_wronskian_derivative (b r : ℝ) (F F₁ G G₁ : ℝ → ℂ)
    (hF : HasDerivAt F (F₁ r) r) (hG : HasDerivAt G (G₁ r) r)
    (hF₁ : HasDerivAt F₁ (-radialFreeCoefficient r*F₁ r-(b : ℂ)*F r) r)
    (hG₁ : HasDerivAt G₁ (-radialFreeCoefficient r*G₁ r-(b : ℂ)*G r) r) :
    HasDerivAt (fun t => F t*G₁ t-F₁ t*G t)
      (-radialFreeCoefficient r*(F r*G₁ r-F₁ r*G r)) r := by
  convert (hF.mul hG₁).sub (hF₁.mul hG) using 1
  ring

theorem radial_free_weighted_wronskian_derivative (b r : ℝ) (hr : r ≠ 0)
    (F F₁ G G₁ : ℝ → ℂ)
    (hF : HasDerivAt F (F₁ r) r) (hG : HasDerivAt G (G₁ r) r)
    (hF₁ : HasDerivAt F₁ (-radialFreeCoefficient r*F₁ r-(b : ℂ)*F r) r)
    (hG₁ : HasDerivAt G₁ (-radialFreeCoefficient r*G₁ r-(b : ℂ)*G r) r) :
    HasDerivAt (fun t => (t^11 : ℝ)*Complex.exp (Complex.I*(t^2/4 : ℝ))*
      (F t*G₁ t-F₁ t*G t)) 0 r := by
  have hw := radial_free_wronskian_derivative b r F F₁ G G₁ hF hG hF₁ hG₁
  have hp := ((hasDerivAt_id r).pow 11).ofReal_comp
  have hq := ((((hasDerivAt_id r).pow 2).div_const 4).ofReal_comp.const_mul Complex.I).cexp
  convert (hp.mul hq).mul hw using 1
  · rfl
  · simp only [Pi.pow_apply,Pi.mul_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one,radialFreeCoefficient]
    push_cast
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    field_simp
    ring

theorem radial_free_wronskian_transport (b l u : ℝ) (hl : 0 < l)
    (F F₁ G G₁ : ℝ → ℂ) (hFc : Continuous F) (hF₁c : Continuous F₁)
    (hGc : Continuous G) (hG₁c : Continuous G₁)
    (hF : ∀ r ∈ Ioo l u, HasDerivAt F (F₁ r) r)
    (hG : ∀ r ∈ Ioo l u, HasDerivAt G (G₁ r) r)
    (hF₁ : ∀ r ∈ Ioo l u, HasDerivAt F₁ (-radialFreeCoefficient r*F₁ r-(b : ℂ)*F r) r)
    (hG₁ : ∀ r ∈ Ioo l u, HasDerivAt G₁ (-radialFreeCoefficient r*G₁ r-(b : ℂ)*G r) r)
    (r : ℝ) (hr : r ∈ Icc l u) :
    (r^11 : ℝ)*Complex.exp (Complex.I*(r^2/4 : ℝ))*(F r*G₁ r-F₁ r*G r)=
      (l^11 : ℝ)*Complex.exp (Complex.I*(l^2/4 : ℝ))*(F l*G₁ l-F₁ l*G l) := by
  have hc : Continuous (fun t => (t^11 : ℝ)*Complex.exp (Complex.I*(t^2/4 : ℝ))*
      (F t*G₁ t-F₁ t*G t)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hc.continuousOn
    (fun t ht => radial_free_weighted_wronskian_derivative b t
      (ne_of_gt (hl.trans ht.1)) F F₁ G G₁
      (hF t ⟨ht.1,ht.2.trans_le hr.2⟩) (hG t ⟨ht.1,ht.2.trans_le hr.2⟩)
      (hF₁ t ⟨ht.1,ht.2.trans_le hr.2⟩) (hG₁ t ⟨ht.1,ht.2.trans_le hr.2⟩))
    (continuous_const.intervalIntegrable l r)
  rw [intervalIntegral.integral_zero] at he
  exact sub_eq_zero.mp he.symm

end DefocusingNLS

end OAI
