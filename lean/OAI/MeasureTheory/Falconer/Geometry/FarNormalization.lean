import OAI.MeasureTheory.Falconer.Estimates.FarRebin
import OAI.MeasureTheory.Falconer.Recursion.ProfileNear

namespace OAI

/-! # Dimensional gain and exact profile normalization of the far term -/

namespace Falconer

theorem far_sphere_gain (m : ℕ) {v b d₁ d₂ : ℝ}
    (h₁ : (2:ℝ)^(-b) ≤ d₁) (h₂ : (2:ℝ)^(-b) ≤ d₂) :
    ((2:ℝ)^v*d₁)^(-((m+2:ℕ):ℝ)/2)*
      ((2:ℝ)^v*d₂)^(-((m+2:ℕ):ℝ)/2) ≤
    (2:ℝ)^(-((m+2:ℕ):ℝ)*(v-b)) := by
  let p : ℝ := -((m+2:ℕ):ℝ)/2
  have hd₁ : 0 ≤ d₁ := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-b)).le.trans h₁
  have hd₂ : 0 ≤ d₂ := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-b)).le.trans h₂
  have hp : p ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num)
  have hbase : (2:ℝ)^v*(2:ℝ)^(-b) = (2:ℝ)^(v-b) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
  have hle (d : ℝ) (hd : (2:ℝ)^(-b) ≤ d) :
      ((2:ℝ)^v*d)^p ≤ ((2:ℝ)^(v-b))^p := by
    apply Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by norm_num) _)
      _ hp
    rw [← hbase]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  change ((2:ℝ)^v*d₁)^p*((2:ℝ)^v*d₂)^p ≤ _
  calc
    _ ≤ ((2:ℝ)^(v-b))^p*((2:ℝ)^(v-b))^p :=
      mul_le_mul (hle d₁ h₁) (hle d₂ h₂) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (v-b)),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      dsimp [p]
      ring

theorem profile_far_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a b : ℕ) (v lam : ℝ) :
    (2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N b/profileModelMass m N a)^4*
      (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(2:ℝ)^(-(v-b))*
      ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-2*((m ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
      (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hfreq : (2:ℝ)^((d:ℝ)*(v-a))*(2:ℝ)^(-((d:ℝ)-1)*(v-b))*
      (2:ℝ)^(-(v-b)) = (2:ℝ)^((d:ℝ)*((b:ℝ)-a)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  calc
    _ = (profileModelMass m N b/profileModelMass m N a)^4*
        ((2:ℝ)^((d:ℝ)*(v-a))*(2:ℝ)^(-((d:ℝ)-1)*(v-b))*(2:ℝ)^(-(v-b)))*
        ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by ring
    _ = _ := by rw [hfreq]; exact profile_near_prefactor hN d m a b lam

end Falconer

end OAI
