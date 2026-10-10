import OAI.MeasureTheory.Falconer.Estimates.EndpointPowerAbsorption
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # The two radial row deletions fit inside the original incidence budget -/

namespace Falconer
open Real Filter
open scoped Topology ENNReal

theorem eventually_endpoint_row_base {u τ c₁ c₂ : ℝ}
    (hu : 0 < u) (hc₁ : τ+10*u < c₁) (hc₂ : τ+10*u < c₂) (V : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4 := by
  have h₀ := eventually_const_mul_rpow_lt (show u < 2*u by linarith) (12*V)
  have h₁ := eventually_const_mul_rpow_lt (show u < c₁-τ-9*u by linarith) (12*V)
  have h₂ := eventually_const_mul_rpow_lt (show u < c₂-τ-9*u by linarith) (12*V)
  filter_upwards [h₀,h₁,h₂] with δ h₀ h₁ h₂
  exact ⟨h₀.1,by nlinarith [h₀.2,h₁.2,h₂.2]⟩

theorem endpoint_row_cost_power {δ : ℝ} (hδ : 0 < δ) (u τ c V : ℝ) :
    δ^(-6*u)*δ^(-3*u)*V*(δ^c/δ^τ) = V*δ^(c-τ-9*u) := by
  rw [← Real.rpow_sub hδ]
  calc
    _ = V*(δ^(-6*u)*δ^(-3*u)*δ^(c-τ)) := by ring
    _ = _ := by rw [← Real.rpow_add hδ,← Real.rpow_add hδ]; congr 1; ring_nf

theorem endpoint_row_base_ennreal {δ u τ c₁ c₂ V : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V)
    (Z A₁ A₂ : ℝ≥0∞) (hZ : Z ≤ ENNReal.ofReal V)
    (hA₁ : A₁ ≤ ENNReal.ofReal (δ^c₁)) (hA₂ : A₂ ≤ ENNReal.ofReal (δ^c₂))
    (hbudget : V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4) :
    ENNReal.ofReal (δ^(2*u))*Z+
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A₁/ENNReal.ofReal (δ^τ))+
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A₂/ENNReal.ofReal (δ^τ)) ≤
        ENNReal.ofReal (δ^u/4) := by
  have hterm (A : ℝ≥0∞) (c : ℝ) (hA : A ≤ ENNReal.ofReal (δ^c)) :
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A/ENNReal.ofReal (δ^τ)) ≤
        ENNReal.ofReal (V*δ^(c-τ-9*u)) := by
    calc
      _ ≤ (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*ENNReal.ofReal V)*
          (ENNReal.ofReal (δ^c)/ENNReal.ofReal (δ^τ)) :=
        mul_le_mul' (mul_le_mul' le_rfl hZ) (ENNReal.div_le_div_right hA _)
      _ = ENNReal.ofReal (δ^(-6*u)*δ^(-3*u)*V*(δ^c/δ^τ)) := by
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hδ _),
          ← ENNReal.ofReal_mul (by positivity)]
      _ = _ := by rw [endpoint_row_cost_power hδ]
  have hb : ENNReal.ofReal (δ^(2*u))*Z ≤ ENNReal.ofReal (V*δ^(2*u)) := by
    calc
      _ ≤ ENNReal.ofReal (δ^(2*u))*ENNReal.ofReal V := mul_le_mul' le_rfl hZ
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity),mul_comm]
  apply (add_le_add (add_le_add hb (hterm A₁ c₁ hA₁)) (hterm A₂ c₂ hA₂)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hbudget

end Falconer

end OAI
