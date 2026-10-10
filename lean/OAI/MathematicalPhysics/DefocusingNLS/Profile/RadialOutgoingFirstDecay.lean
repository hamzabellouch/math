import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorAllOrders

namespace OAI

/-! The actual nonlinear outgoing jet has the first two-power improvement. -/

open Set Filter Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialPolynomialJet_sub_constant (P : ℂ[X]) (m : ℂ) (t : ℝ) :
    radialPolynomialJet (P-C m) t=radialPolynomialJet P t-(m,0) := by
  apply Prod.ext
  · simp [radialPolynomialJet,radialExteriorPolynomialFunction]
  · simp [radialPolynomialJet,radialPolynomialEuler,radialExteriorPolynomialFunction,
      derivative_sub]

theorem radialExteriorCanonical_first_decay (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in atTop,
      ‖radialExteriorCanonical ν n m L t-(m,0)‖ ≤ C*Real.exp (-2*t) := by
  obtain ⟨j,hj,v,T,hT⟩ := radialExteriorCanonical_allOrders ν m n L hX hm 1
  let P := radialExteriorExpansion ν n m j
  have hP : X^1 ∣ P-C m := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    simp [P,radialExteriorExpansion_constant]
  obtain ⟨C,hC,hB⟩ := radialPolynomialJet_factor_decay (P-C m) 1 hP
  refine ⟨C+‖v‖,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop T,eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hp := hB t ht0
  rw [radialPolynomialJet_sub_constant] at hp
  have he : Real.exp (-(2*(j : ℝ))*t) ≤ Real.exp (-2*t) := by
    apply Real.exp_le_exp.mpr
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hv : ‖radialExteriorUnweight (2*(j : ℝ)) v t‖ ≤ ‖v‖*Real.exp (-2*t) := by
    exact (radialExteriorUnweight_norm _ t v ‖v‖ (v.norm_coe_le_norm t)).trans
      ((mul_le_mul_of_nonneg_right he (norm_nonneg v)).trans_eq (mul_comm _ _))
  rw [hT t ht]
  calc
    ‖radialPolynomialJet P t+radialExteriorUnweight (2*(j : ℝ)) v t-(m,0)‖ =
        ‖(radialPolynomialJet P t-(m,0))+radialExteriorUnweight (2*(j : ℝ)) v t‖ := by
          congr 1
          abel
    _ ≤ ‖radialPolynomialJet P t-(m,0)‖+‖radialExteriorUnweight (2*(j : ℝ)) v t‖ := norm_add_le _ _
    _ ≤ C*Real.exp (-2*t)+‖v‖*Real.exp (-2*t) := by
      exact add_le_add (by simpa using hp) hv
    _ = _ := by ring

theorem radialExteriorCanonical_velocity_decay (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in atTop,
      ‖(radialExteriorCanonical ν n m L t).2‖ ≤ C*Real.exp (-2*t) := by
  obtain ⟨C,hC,hB⟩ := radialExteriorCanonical_first_decay ν m n L hX hm
  refine ⟨C,hC,?_⟩
  filter_upwards [hB] with t ht
  have hh : ‖(radialExteriorCanonical ν n m L t).2‖ ≤
      ‖radialExteriorCanonical ν n m L t-(m,0)‖ := by
    have hp := norm_snd_le (radialExteriorCanonical ν n m L t-(m,0))
    change ‖(radialExteriorCanonical ν n m L t).2-(0 : ℂ)‖ ≤ _ at hp
    simpa only [sub_zero] using hp
  exact hh.trans ht

end DefocusingNLS

end OAI
