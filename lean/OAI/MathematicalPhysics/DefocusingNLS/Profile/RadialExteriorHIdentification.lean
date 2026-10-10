import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFreeUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowJet

namespace OAI

/-! Identify the constructed free correction with the actual outgoing H solution. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_free_difference_hasDerivAt (ν : ℂ)
    (Z W : ℝ → ℂ × ℂ) (t : ℝ)
    (hZ : HasDerivAt Z ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
      radialExteriorErrorMatrix ν (Z t)) t)
    (hW : HasDerivAt W ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(W t).2)+
      radialExteriorErrorMatrix ν (W t)) t) :
    HasDerivAt (fun s => Z s-W s)
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t-W t).2)+
        radialExteriorErrorMatrix ν (Z t-W t)) t := by
  apply (hZ.sub hW).congr_deriv
  rw [map_sub]
  apply Prod.ext
  all_goals simp
  ring

theorem radialExterior_free_correction_eq_H (q m : ℂ) (hq : -1 < q.re)
    (j : ℕ) (T : ℝ) (w : ℝ →ᵇ ℂ × ℂ)
    (hκ : radialExteriorMatrixBound (-2*q) < 2*((j+1 : ℕ) : ℝ))
    (hODE : ∀ t, T ≤ t → HasDerivAt
      (fun s => radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) s+
        radialExteriorUnweight (2*((j+1 : ℕ) : ℝ)) w s)
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*
          (radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) t+
            radialExteriorUnweight (2*((j+1 : ℕ) : ℝ)) w t).2)+
        radialExteriorErrorMatrix (-2*q)
          (radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) t+
            radialExteriorUnweight (2*((j+1 : ℕ) : ℝ)) w t)) t) :
    ∀ t, max T (max 0 (Real.log 4/2)) ≤ t →
      radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) t+
        radialExteriorUnweight (2*((j+1 : ℕ) : ℝ)) w t=radialFreeSlowJet q m t := by
  obtain ⟨C,hC,hrem⟩ := radialFreeSlowJet_remainder q m hq j
  let κ : ℝ := 2*((j+1 : ℕ) : ℝ)
  let Z : ℝ → ℂ × ℂ := fun s =>
    radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) s+radialExteriorUnweight κ w s
  let D : ℝ → ℂ × ℂ := fun s => Z s-radialFreeSlowJet q m s
  let S := max T (max 0 (Real.log 4/2))
  have hDS : ∀ s, S ≤ s → HasDerivAt D
      ((0,-Complex.I*(Real.exp (2*s)/2 : ℝ)*(D s).2)+radialExteriorErrorMatrix (-2*q) (D s)) s := by
    intro s hs
    exact radialExterior_free_difference_hasDerivAt (-2*q) Z (radialFreeSlowJet q m) s
      (hODE s ((le_max_left T _).trans hs)) (radialFreeSlowJet_hasDerivAt q m hq s)
  have hdec : ∀ s, S ≤ s → ‖D s‖ ≤ (‖w‖+C)*Real.exp (-κ*s) := by
    intro s hs
    have hs0 : 0 ≤ s := ((le_max_left 0 _).trans (le_max_right T _)).trans hs
    have hslog : Real.log 4/2 ≤ s := ((le_max_right 0 _).trans (le_max_right T _)).trans hs
    have he : Real.exp (-(2*((j+2 : ℕ) : ℝ))*s) ≤ Real.exp (-κ*s) := by
      apply Real.exp_le_exp.mpr
      dsimp [κ]
      push_cast
      nlinarith
    calc
      ‖D s‖ ≤ ‖radialExteriorUnweight κ w s‖+
          ‖radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) s-radialFreeSlowJet q m s‖ := by
        dsimp [D,Z]
        convert norm_add_le (radialExteriorUnweight κ w s)
          (radialPolynomialJet (radialFreeExpansion (-2*q) m (j+1)) s-radialFreeSlowJet q m s) using 1
        abel_nf
      _ ≤ Real.exp (-κ*s)*‖w‖+C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*s) := by
        apply add_le_add (radialExteriorUnweight_norm κ s w ‖w‖ (w.norm_coe_le_norm s))
        rw [norm_sub_rev]
        exact hrem s hslog
      _ ≤ Real.exp (-κ*s)*‖w‖+C*Real.exp (-κ*s) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left he hC)
      _ = _ := by ring
  intro t ht
  exact sub_eq_zero.mp (radialExterior_free_fast_decay_zero (-2*q) D κ (‖w‖+C) S hDS hdec hκ t ht)

end DefocusingNLS

end OAI
