import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowAsymptotic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit

namespace OAI

/-! The actual H value/velocity jet and its complete finite-order outgoing expansion. -/

namespace DefocusingNLS

noncomputable def radialFreeSlowJet (q m : ℂ) (t : ℝ) : ℂ × ℂ :=
  (radialFreeSlowValue q m t,radialFreeSlowVelocity q m t)

theorem radialFreeSlowJet_hasDerivAt (q m : ℂ) (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (radialFreeSlowJet q m)
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(radialFreeSlowJet q m t).2)+
        radialExteriorErrorMatrix (-2*q) (radialFreeSlowJet q m t)) t := by
  have h := (hasDerivAt_radialFreeSlowValue q m hq t).prodMk
    (hasDerivAt_radialFreeSlowVelocity q m hq t)
  apply h.congr_deriv
  apply Prod.ext
  · simp [radialFreeSlowJet,radialExteriorErrorMatrix]
  · simp only [radialFreeSlowJet,Prod.snd_add,radialExteriorErrorMatrix,
      ContinuousLinearMap.prod_apply,neg_apply,
      add_apply,smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    ring

theorem radialFreeSlowJet_remainder (q m : ℂ) (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖radialFreeSlowJet q m t-radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) t‖ ≤
        C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*t) := by
  obtain ⟨A,hA,hv⟩ := radialFreeSlowValue_remainder q m hq (j+1)
  obtain ⟨B,hB,hw⟩ := radialFreeSlowVelocity_remainder q m hq j
  refine ⟨max A B,le_max_of_le_left hA,?_⟩
  intro t ht
  change max ‖radialFreeSlowValue q m t-radialExteriorPolynomialFunction _ t‖
    ‖radialFreeSlowVelocity q m t-radialExteriorPolynomialFunction _ t‖ ≤ _
  apply max_le
  · exact (hv t ht).trans (mul_le_mul_of_nonneg_right (le_max_left A B) (Real.exp_nonneg _))
  · exact (hw t ht).trans (mul_le_mul_of_nonneg_right (le_max_right A B) (Real.exp_nonneg _))

end DefocusingNLS

end OAI
