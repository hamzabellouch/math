import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPicard
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailDerivative

namespace OAI

/-! Quantitative existence for the actual backward weighted differential equation. -/

open Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_fixedPoint_bound (κ L C : ℝ) (hκ : 0 < κ) (hL : 0 ≤ L)
    (hLκ : L < κ) (hC : 0 ≤ C)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : ℝ →ᵇ ℂ × ℂ)
    (hv : ∀ t, v t=radialExteriorTailIntegral κ (fun s => N s (v s)) t) :
    ‖v‖ ≤ C/(κ-L) := by
  have heq : v=radialExteriorPicard κ L C hκ hL N hN hN0 hLip v := by
    apply BoundedContinuousFunction.ext
    intro t
    exact hv t
  have hb := boundedRadialExteriorTail_norm κ hκ
    (boundedRadialExteriorSource L C hL N hN hN0 hLip v)
  change ‖radialExteriorPicard κ L C hκ hL N hN hN0 hLip v‖ ≤ _ at hb
  rw [← heq] at hb
  have hsource := boundedRadialExteriorSource_norm L C hL hC N hN hN0 hLip v
  have hh : κ*‖v‖ ≤ L*‖v‖+C := by
    have hh := (le_div_iff₀ hκ).mp (hb.trans
      (div_le_div_of_nonneg_right hsource hκ.le))
    nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hLκ)).mpr
  nlinarith

theorem exists_radialExterior_weighted_ODE (κ L C : ℝ) (hκ : 0 < κ)
    (hL : 0 ≤ L) (hLκ : L < κ) (hC : 0 ≤ C)
    (N : ℝ → (ℂ × ℂ) → ℂ × ℂ) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖) :
    ∃ v : ℝ →ᵇ ℂ × ℂ, ‖v‖ ≤ C/(κ-L) ∧
      (∀ t, v t=radialExteriorTailIntegral κ (fun s => N s (v s)) t) ∧
      ∀ t, HasDerivAt (fun r => v r)
        (κ • v t + (0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2) + N t (v t)) t := by
  obtain ⟨v,hv,_⟩ := existsUnique_radialExteriorTail κ L C hκ hL hLκ N hN hN0 hLip
  refine ⟨v,radialExterior_fixedPoint_bound κ L C hκ hL hLκ hC N hN hN0 hLip v hv,hv,?_⟩
  intro t
  let w := boundedRadialExteriorSource L C hL N hN hN0 hLip v
  have hd := radialExteriorTailIntegral_hasDerivAt κ ‖w‖ t hκ w w.continuous w.norm_coe_le_norm
  have heq : (fun r => v r)=radialExteriorTailIntegral κ w := funext hv
  rw [← heq] at hd
  exact hd

end DefocusingNLS

end OAI
