import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorErrorField
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCutoff

namespace OAI

/-! The exterior error equation with the actual odd-power polynomial on its unclipped region. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorCutoffRate (n : ℕ) (m : ℂ) (δ : ℝ) : ℝ :=
  2*(2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n)

theorem radialExteriorCutoffRate_nonneg (n : ℕ) (m : ℂ) (δ : ℝ) :
    0 ≤ radialExteriorCutoffRate n m δ := by
  unfold radialExteriorCutoffRate
  rw [pow_mul]
  positivity

theorem radialExteriorCutoffRate_tendsto (m : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : ‖m‖+2*δ < 1) :
    Filter.Tendsto (fun n => radialExteriorCutoffRate n m δ) Filter.atTop (nhds 0) := by
  convert (radial_oddPower_lipschitz_tendsto (‖m‖+2*δ) (by positivity) hsmall).const_mul 2 using 1
  · funext n
    unfold radialExteriorCutoffRate
    ring
  · ring_nf

theorem exists_radialExterior_nonlinear_tail (κ : ℝ) (ν : ℂ) (n : ℕ)
    (m : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hκ : radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ < κ)
    (f : ℝ → ℂ) (hf : Continuous f) (r : ℝ →ᵇ ℂ × ℂ) :
    ∃ v : ℝ →ᵇ ℂ × ℂ,
      ‖v‖ ≤ ‖r‖/(κ-(radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ)) ∧
      ∀ t, HasDerivAt (fun s => v s)
        (κ • v t + (0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2) +
          radialExteriorErrorField κ ν (radialExteriorCutoffPower n m δ) f r t (v t)) t := by
  have hL := radialExteriorCutoffRate_nonneg n m δ
  have htotal : 0 ≤ radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ :=
    add_nonneg (radialExteriorMatrixBound_pos ν).le hL
  obtain ⟨v,hv,_,hd⟩ := exists_radialExterior_weighted_ODE κ
    (radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ) ‖r‖
    (lt_of_le_of_lt htotal hκ) htotal hκ (norm_nonneg _)
    (radialExteriorErrorField κ ν (radialExteriorCutoffPower n m δ) f r)
    (radialExteriorErrorField_continuous κ ν _ (radialExteriorCutoffPower_continuous n m δ) f hf r)
    (fun t => by rw [radialExteriorErrorField_zero]; exact r.norm_coe_le_norm t)
    (radialExteriorErrorField_difference κ _ hL ν _
      (radialExteriorCutoffPower_difference n m δ hδ) f r)
  exact ⟨v,hv,hd⟩

end DefocusingNLS

end OAI
