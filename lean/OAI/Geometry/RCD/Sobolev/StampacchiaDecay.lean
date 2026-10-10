import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Geometric decay in the torsion superlevel iteration -/

open Filter
open scoped Topology

namespace RegularPointCoordinates

/-- The superlinear recurrence contracts once its initial coefficient and
geometric amplification satisfy the displayed scalar bounds. -/
theorem power_recurrence_decay {Y : ℕ → ℝ} {A B V θ q : ℝ}
    (hY : ∀ j, 0 ≤ Y j) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hV : 0 < V) (hθ : 0 < θ) (hq : 1 < q)
    (hstart : Y 0 ≤ V) (hsmall : A * V ^ (q - 1) ≤ θ)
    (hamp : B * θ ^ (q - 1) ≤ 1)
    (hstep : ∀ j, Y (j + 1) ≤ A * B ^ j * (Y j) ^ q) :
    ∀ j, Y j ≤ V * θ ^ j := by
  intro j
  induction j with
  | zero => simpa using hstart
  | succ j ih =>
    have hVp : V ^ q = V ^ (q - 1) * V := by
      calc
        V ^ q = V ^ ((q - 1) + 1) := by congr 1; ring
        _ = V ^ (q - 1) * V := by rw [Real.rpow_add hV, Real.rpow_one]
    have hθp : θ ^ q = θ ^ (q - 1) * θ := by
      calc
        θ ^ q = θ ^ ((q - 1) + 1) := by congr 1; ring
        _ = θ ^ (q - 1) * θ := by rw [Real.rpow_add hθ, Real.rpow_one]
    have hpowers : (θ ^ j) ^ q = (θ ^ q) ^ j := by
      rw [← Real.rpow_natCast_mul hθ.le, mul_comm (j : ℝ) q, Real.rpow_mul_natCast hθ.le]
    have hfac : A * B ^ j * (V * θ ^ j) ^ q =
        (A * V ^ (q - 1)) * V * (B * θ ^ (q - 1)) ^ j * θ ^ j := by
      rw [Real.mul_rpow hV.le (pow_nonneg hθ.le _), hpowers, hVp, hθp]
      simp only [mul_pow]
      ring
    calc
      Y (j + 1) ≤ A * B ^ j * (Y j) ^ q := hstep j
      _ ≤ A * B ^ j * (V * θ ^ j) ^ q :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hY j) ih (by linarith))
          (mul_nonneg hA (pow_nonneg hB _))
      _ = (A * V ^ (q - 1)) * V * (B * θ ^ (q - 1)) ^ j * θ ^ j := hfac
      _ ≤ θ * V * 1 * θ ^ j := by
        gcongr
        exact pow_le_one₀ (mul_nonneg hB (Real.rpow_nonneg hθ.le _)) hamp
      _ = V * θ ^ (j + 1) := by rw [pow_succ]; ring

/-- A nonnegative number below every term of a decaying geometric majorant
is zero. -/
theorem eq_zero_of_le_geometric {a V θ : ℝ} (ha : 0 ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hle : ∀ j : ℕ, a ≤ V * θ ^ j) : a = 0 := by
  have ht : Tendsto (fun j : ℕ => V * θ ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hle)) ha

end RegularPointCoordinates

end OAI
