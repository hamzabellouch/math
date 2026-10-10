import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Scalar estimates for a heavy set of return indices

If a set contains more than `k / M` indices and `2 * M ≤ k`, its cardinality
minus one controls the length of the ambient progression. These estimates
convert the span bounds into the rate and gap bounds used for closest returns.
-/

namespace QuantitativeVanDerWaerden

/-- A heavy set has at least two points and a positive span. The span is large
enough to absorb the ambient length after multiplication by `2 * M`. -/
theorem heavy_card_estimates {M : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ)) :
    2 ≤ m ∧ 0 < (m : ℝ) - 1 ∧
      (k : ℝ) ≤ ((m : ℝ) - 1) * (2 * M) ∧ 0 < k := by
  have hkR : 0 < (k : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num) hM) hscale
  have hkm : (k : ℝ) < (m : ℝ) * M := (div_lt_iff₀ hM).mp hheavy
  have hmR : (2 : ℝ) < (m : ℝ) :=
    (mul_lt_mul_iff_left₀ hM).mp (hscale.trans_lt hkm)
  have hmNat : 2 ≤ m := by exact_mod_cast hmR.le
  have hspan : 0 < (m : ℝ) - 1 := by linarith only [hmR]
  have hlower : (k : ℝ) ≤ ((m : ℝ) - 1) * (2 * M) := by
    nlinarith only [hscale, hkm]
  have hkNat : 0 < k := by exact_mod_cast hkR
  exact ⟨hmNat, hspan, hlower, hkNat⟩

/-- Division form of the lower bound on the cardinality minus one. -/
theorem heavy_card_div_lower {M : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ)) :
    (k : ℝ) / (2 * M) ≤ (m : ℝ) - 1 := by
  obtain ⟨_, _, hlower, _⟩ := heavy_card_estimates hM hscale hheavy
  exact (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr hlower

/-- A nonnegative displacement divided by the heavy-set span has rate at most
`2 * M` times the displacement divided by the ambient length. -/
theorem heavy_card_rate_le {M L : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ)) (hL : 0 ≤ L) :
    L / ((m : ℝ) - 1) ≤ 2 * M * L / (k : ℝ) := by
  obtain ⟨_, hspan, hlower, hk⟩ := heavy_card_estimates hM hscale hheavy
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (div_le_div_iff₀ hspan hkR).mpr
  calc
    L * (k : ℝ) ≤ L * (((m : ℝ) - 1) * (2 * M)) :=
      mul_le_mul_of_nonneg_left hlower hL
    _ = (2 * M * L) * ((m : ℝ) - 1) := by ring

/-- A gap whose product with the heavy-set span fits in the ambient length is
at most `2 * M`. This bound does not require the gap to be nonnegative. -/
theorem heavy_card_gap_le {M h : ℝ} {k m : ℕ}
    (hM : 0 < M) (hscale : 2 * M ≤ (k : ℝ))
    (hheavy : (k : ℝ) / M < (m : ℝ))
    (hstep : h * ((m : ℝ) - 1) ≤ (k : ℝ)) :
    h ≤ 2 * M := by
  obtain ⟨_, hspan, hlower, _⟩ := heavy_card_estimates hM hscale hheavy
  apply (mul_le_mul_iff_left₀ hspan).mp
  calc
    h * ((m : ℝ) - 1) ≤ (k : ℝ) := hstep
    _ ≤ ((m : ℝ) - 1) * (2 * M) := hlower
    _ = (2 * M) * ((m : ℝ) - 1) := mul_comm _ _

end QuantitativeVanDerWaerden

end OAI
