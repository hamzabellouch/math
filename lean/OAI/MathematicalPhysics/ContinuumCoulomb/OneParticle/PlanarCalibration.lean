import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHoppingBounds
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Endpoint brackets and an actual contact-hopping calibration. Quantitative
scale selection and the polynomial-time numerical implementation remain
separate steps; no calibration output is assumed. -/

noncomputable section
namespace ContinuumCoulomb

theorem planarHopping_short_scaled {D ε : ℝ} (hd : 2 ≤ (1 - ε) * D) :
    planarHoppingLowerConstant / ((1 - ε) * D + 3) * Real.exp (ε * D) ≤
      Real.exp D * planarHopping ((1 - ε) * D) := by
  have h := mul_le_mul_of_nonneg_left (planarHopping_sharp_lower hd) (Real.exp_pos D).le
  convert h using 1
  calc
    _ = (planarHoppingLowerConstant / ((1 - ε) * D + 3)) *
        (Real.exp D * Real.exp (-((1 - ε) * D))) := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring
    _ = _ := by ring

theorem planarHopping_long_scaled {D ε : ℝ} (hd : 2 ≤ (1 + ε) * D) :
    Real.exp D * planarHopping ((1 + ε) * D) ≤
      planarHoppingUpperConstant * ((1 + ε) * D + 1) * Real.exp (-ε * D) := by
  have h := mul_le_mul_of_nonneg_left (planarHopping_sharp_upper hd) (Real.exp_pos D).le
  convert h using 1
  calc
    _ = (planarHoppingUpperConstant * ((1 + ε) * D + 1)) *
        (Real.exp D * Real.exp (-((1 + ε) * D))) := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring
    _ = _ := by ring

/-- The paper's actual hopping profile attains the distance-dependent
superexchange target inside the permitted contact-length interval. Only
continuity of the direct Coulomb profile and the explicit endpoint numerical
brackets remain as premises here. -/
theorem planarHopping_contact_calibration {D ε τ K U : ℝ} (v : ℝ → ℝ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hd : 2 ≤ (1 - ε) * D)
    (hv : ContinuousOn v (Set.Icc ((1 - ε) * D) ((1 + ε) * D)))
    (hshort : τ * Real.sqrt (K * (U - v ((1 - ε) * D))) ≤
      planarHoppingLowerConstant / ((1 - ε) * D + 3) * Real.exp (ε * D))
    (hlong : planarHoppingUpperConstant * ((1 + ε) * D + 1) * Real.exp (-ε * D) ≤
      τ * Real.sqrt (K * (U - v ((1 + ε) * D)))) :
    ∃ d ∈ Set.Icc ((1 - ε) * D) ((1 + ε) * D),
      Real.exp D * planarHopping d = τ * Real.sqrt (K * (U - v d)) := by
  have hab : (1 - ε) * D ≤ (1 + ε) * D := by nlinarith
  have hlong₂ : 2 ≤ (1 + ε) * D := hd.trans hab
  let F : ℝ → ℝ := fun d => Real.exp D * planarHopping d - τ * Real.sqrt (K * (U - v d))
  have hc : ContinuousOn F (Set.Icc ((1 - ε) * D) ((1 + ε) * D)) :=
    (continuous_const.mul planarHopping_lipschitz.continuous).continuousOn.sub
      (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.sub hv))))
  have h₀ : F ((1 + ε) * D) ≤ 0 := by
    have h := (planarHopping_long_scaled hlong₂).trans hlong
    dsimp [F]
    linarith
  have h₁ : 0 ≤ F ((1 - ε) * D) := by
    have h := hshort.trans (planarHopping_short_scaled hd)
    dsimp [F]
    linarith
  obtain ⟨d, hdmem, heq⟩ := intermediate_value_Icc' hab hc ⟨h₀, h₁⟩
  exact ⟨d, hdmem, sub_eq_zero.mp heq⟩

end ContinuumCoulomb

end

end OAI
