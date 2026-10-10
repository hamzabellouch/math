import OAI.MeasureTheory.Falconer.Graphs.ProfileGraph
import OAI.MeasureTheory.Falconer.Graphs.GraphTwoErrors

namespace OAI

/-! # The model masses pay for both graph errors

The child masses cancel before estimating. Only the two parent profile
values remain, so the combined normalization costs at most R^(5d).
-/

namespace Falconer

theorem graph_error_mass_cancellation {M₁ M₂ U₁ U₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    ((U₁/M₁)*(U₂/M₂))^2 * |(U₁⁻¹*U₁⁻¹)*(U₂⁻¹*U₂⁻¹)| =
      (M₁⁻¹)^2*(M₂⁻¹)^2 := by
  rw [abs_of_pos (by positivity)]
  field_simp

theorem profile_graph_error_weight_bound (d : ℕ) {N a p : ℕ}
    (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) {v : ℝ} (hv : v ≤ N)
    (hm₁ : m₁ ((a:ℝ)/N) ≤ d) (hm₂ : m₂ ((a:ℝ)/N) ≤ d) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        |((profileModelMass m₁ N p)⁻¹*(profileModelMass m₁ N p)⁻¹)*
          ((profileModelMass m₂ N p)⁻¹*(profileModelMass m₂ N p)⁻¹)| ≤
      ((2:ℝ)^N)^(5*(d:ℝ)) := by
  have hM (m : ℝ → ℝ) (j : ℕ) : 0 < profileModelMass m N j := by
    unfold profileModelMass
    positivity
  have hR : 0 < (2:ℝ)^N := by positivity
  have hRone : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hm (m : ℝ → ℝ) : ((profileModelMass m N a)⁻¹)^2 =
      ((2:ℝ)^N)^(2*m ((a:ℝ)/N)) := by
    unfold profileModelMass
    rw [← Real.rpow_neg hR.le,← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [mul_assoc,graph_error_mass_cancellation (hM m₁ a) (hM m₂ a) (hM m₁ p) (hM m₂ p),
    hm m₁,hm m₂,← dyadic_rpow_change_base hN ((d:ℝ)*(v-a)),
    ← mul_assoc,← Real.rpow_add hR,← Real.rpow_add hR]
  apply Real.rpow_le_rpow_of_exponent_le hRone
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hfrac : (d:ℝ)*(v-a)/N ≤ d := by
    apply (div_le_iff₀ hNR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d,Nat.cast_nonneg (α := ℝ) a]
  linarith

end Falconer

end OAI
