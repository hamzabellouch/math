import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem abs_sub_lt_of_floor_div_eq {r s ε : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hε : 0 < ε)
    (heq : Nat.floor (r / ε) = Nat.floor (s / ε)) : |r - s| < ε := by
  have hrlo : (Nat.floor (r / ε) : ℝ) * ε ≤ r :=
    (le_div_iff₀ hε).mp (Nat.floor_le (div_nonneg hr hε.le))
  have hrhi : r < ((Nat.floor (r / ε) : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (r / ε))
  have hslo : (Nat.floor (s / ε) : ℝ) * ε ≤ s :=
    (le_div_iff₀ hε).mp (Nat.floor_le (div_nonneg hs hε.le))
  have hshi : s < ((Nat.floor (s / ε) : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (s / ε))
  rw [heq] at hrlo hrhi
  rw [abs_sub_lt_iff]
  constructor <;> nlinarith

def orderedIntervalLabel (A ε : ℝ) (hε : 0 < ε) :
    Set.Icc (0 : ℝ) A → Fin (Nat.floor (A / ε) + 1) :=
  fun r => ⟨Nat.floor ((r : ℝ) / ε), Nat.lt_succ_of_le
    (Nat.floor_le_floor (div_le_div_of_nonneg_right r.property.2 hε.le))⟩

theorem monotone_orderedIntervalLabel (A ε : ℝ) (hε : 0 < ε) :
    Monotone (orderedIntervalLabel A ε hε) := by
  intro r s hrs
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right hrs hε.le)

theorem orderedIntervalLabel_small_fiber (A ε : ℝ) (hε : 0 < ε)
    {r s : Set.Icc (0 : ℝ) A}
    (heq : orderedIntervalLabel A ε hε r = orderedIntervalLabel A ε hε s) :
    |(r : ℝ) - (s : ℝ)| < ε := by
  exact abs_sub_lt_of_floor_div_eq r.property.1 s.property.1 hε (congrArg Fin.val heq)

theorem exists_monotone_interval_labels (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, ∃ b : Set.Icc (0 : ℝ) A → Fin (H + 1),
      Monotone b ∧ ∀ r s, b r = b s → |(r : ℝ) - (s : ℝ)| < ε := by
  exact ⟨Nat.floor (A / ε), orderedIntervalLabel A ε hε,
    monotone_orderedIntervalLabel A ε hε,
    fun _ _ heq => orderedIntervalLabel_small_fiber A ε hε heq⟩

end Problem340

end

end OAI
