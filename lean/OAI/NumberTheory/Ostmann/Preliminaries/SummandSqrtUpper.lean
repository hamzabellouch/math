import Mathlib.Data.Nat.Sqrt
import OAI.NumberTheory.Ostmann.Preliminaries.SummandSquareUpper

namespace OAI

/-! # Passing the summand upper bound from squares to every cutoff -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_sqrt_upper {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((summandPrefix A N).card : ℝ) ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hupper⟩ := h.summand_square_upper hB
  have htend : Tendsto (fun N : ℕ => N.sqrt + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b ^ 2)] with N hN
    have hh := Nat.le_sqrt'.mpr hN
    omega
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [htend.eventually hupper, eventually_ge_atTop (2 : ℕ)] with N hu hN
  let q := N.sqrt + 1
  have hqp : (0 : ℝ) < q := by dsimp [q]; positivity
  have hqN : q ≤ N := by
    dsimp [q]
    have hh := Nat.sqrt_lt_self (by omega : 1 < N)
    omega
  have hNN : N ≤ q ^ 2 := (Nat.lt_succ_sqrt' N).le
  have hprefix : summandPrefix A N ⊆ summandPrefix A (q ^ 2) := by
    intro a ha
    obtain ⟨ha, han⟩ := mem_summandPrefix A N a |>.mp ha
    exact mem_summandPrefix A (q ^ 2) a |>.mpr ⟨ha, han.trans hNN⟩
  have hc : ((summandPrefix A N).card : ℝ) ≤ (summandPrefix A (q ^ 2)).card := by
    exact_mod_cast Finset.card_le_card hprefix
  have hroot : (q : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    have hh : (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
    have hone : 1 ≤ Real.sqrt (N : ℝ) :=
      (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by exact_mod_cast (by omega : 1 ≤ N))
    dsimp [q]
    push_cast
    linarith
  have hlog : Real.log (q : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hqp (by exact_mod_cast hqN)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by dsimp [q]; norm_cast; omega)
  calc
    _ ≤ ((summandPrefix A (q ^ 2)).card : ℝ) := hc
    _ ≤ C * q * Real.log (q : ℝ) ^ 2 := hu
    _ ≤ C * (2 * Real.sqrt (N : ℝ)) * Real.log (N : ℝ) ^ 2 := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
