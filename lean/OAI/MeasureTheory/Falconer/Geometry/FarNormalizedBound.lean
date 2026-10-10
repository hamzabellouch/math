import OAI.MeasureTheory.Falconer.Fourier.FarCollisionIntegral
import OAI.MeasureTheory.Falconer.Recursion.FarProfileNormalization

namespace OAI

/-! # Collision normalization and the two-free-cell count in one far bound -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

private theorem real_scaled_bound {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (_hγ : 0 ≤ γ) {I X : ℝ≥0∞}
    (h : ENNReal.ofReal β * I ≤ ENNReal.ofReal γ * X) :
    ENNReal.ofReal α * I ≤ ENNReal.ofReal (α*γ/β) * X := by
  have hab : 0 ≤ α/β := div_nonneg hα hβ.le
  calc
    _ = ENNReal.ofReal (α/β) * (ENNReal.ofReal β * I) := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hab,div_mul_cancel₀ α hβ.ne']
    _ ≤ ENNReal.ofReal (α/β) * (ENNReal.ofReal γ * X) := mul_le_mul' le_rfl h
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hab]
      congr 2
      ring

 theorem profile_far_collision_bound {N : ℕ} (hN : 0 < N)
    (d : ℕ) (profile : ℝ → ℝ) (a b : ℕ) (v lam : ℝ)
    {C Cdim : ℝ} (hC : 0 ≤ C) (hCdim : 0 ≤ Cdim)
    {card : ℕ}
    (hcard : (card:ℝ) ≤ Cdim*((2:ℝ)^N)^(
      2*(profile ((b:ℝ)/N)-profile ((a:ℝ)/N))+4*((d:ℝ)+1)*lam))
    {I X : ℝ≥0∞}
    (h : ENNReal.ofReal ((2:ℝ)^(v-b)*(profileModelMass profile N b)⁻¹^4)*I ≤
      ENNReal.ofReal (C*(2:ℝ)^(-((d:ℝ)-1)*(v-b)))*(card:ℝ≥0∞)*X) :
    ENNReal.ofReal ((2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4)*I ≤
      ENNReal.ofReal (C*Cdim*((2:ℝ)^N)^(
        -2*((profile ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
          (profile ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam))*X := by
  let α := (2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4
  let β := (2:ℝ)^(v-b)*(profileModelMass profile N b)⁻¹^4
  let G := (2:ℝ)^(-((d:ℝ)-1)*(v-b))
  let R := ((2:ℝ)^N)^(2*(profile ((b:ℝ)/N)-profile ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β,profileModelMass]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc : (card:ℝ≥0∞) ≤ ENNReal.ofReal (Cdim*R) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
  have h' : ENNReal.ofReal β*I ≤ ENNReal.ofReal (C*G*Cdim*R)*X := by
    calc
      _ ≤ ENNReal.ofReal (C*G)*(card:ℝ≥0∞)*X := h
      _ ≤ ENNReal.ofReal (C*G)*ENNReal.ofReal (Cdim*R)*X :=
        mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl
      _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hC hG)]; congr 2; ring
  have hscale := real_scaled_bound hα hβ
    (mul_nonneg (mul_nonneg (mul_nonneg hC hG) hCdim) hR) h'
  have he : α*(C*G*Cdim*R)/β = C*Cdim*((2:ℝ)^N)^(
        -2*((profile ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
          (profile ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
    calc
      _ = C*Cdim*((α*G/β)*R) := by ring
      _ = _ := by rw [profile_far_collision_normalization hN d profile a b v lam]
  simpa only [he,α] using hscale

end Falconer

end OAI
