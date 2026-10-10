import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Finite quantiles for the fourth-moment gap

The lower and upper quantile choices in the proof of `phase:quantile-gap`, §7.
Weights are listed in increasing frequency order. No uniform measure on the
frequency list is assumed.
-/

open scoped BigOperators

namespace LipschitzHilbert

def prefixMass (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, w i

theorem prefixMass_succ (w : ℕ → ℝ) (n : ℕ) :
    prefixMass w (n + 1) = prefixMass w n + w n := Finset.sum_range_succ _ _

theorem prefixMass_mono {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Monotone (prefixMass w) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun i _ _ => hw i)

/-- The first cumulative crossing has an atom on its right and a strict
inequality immediately to its left. -/
theorem exists_first_crossing (w : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht : 0 < t) (htN : t ≤ prefixMass w N) :
    ∃ a < N, prefixMass w a < t ∧ t ≤ prefixMass w (a + 1) := by
  classical
  let hex : ∃ n : ℕ, t ≤ prefixMass w n := ⟨N, htN⟩
  let k := Nat.find hex
  have hk : t ≤ prefixMass w k := Nat.find_spec hex
  have hkN : k ≤ N := Nat.find_min' hex htN
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    simp [hz, prefixMass] at hk
    linarith
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (show k - 1 < k by omega))
  · simpa [show k - 1 + 1 = k by omega] using hk

/-- Nonconcentration of single atoms forces the two quarter-tail quantiles
to be distinct. The inequalities also bound the mass outside their interval. -/
theorem exists_distinct_quantiles (w : ℕ → ℝ) (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hw : ∀ i, 0 ≤ w i)
    (htotal : prefixMass w N = 1) (hatom : ∀ i < N, w i ≤ 1 - κ) :
    ∃ a b : ℕ, a < b ∧ b < N ∧
      prefixMass w a < κ / 4 ∧ κ / 4 ≤ prefixMass w (a + 1) ∧
      prefixMass w b < 1 - κ / 4 ∧ 1 - κ / 4 ≤ prefixMass w (b + 1) ∧
      1 - κ / 2 ≤ prefixMass w (b + 1) - prefixMass w a := by
  obtain ⟨a, haN, ha, ha'⟩ := exists_first_crossing w N
    (show 0 < κ / 4 by linarith) (show κ / 4 ≤ prefixMass w N by rw [htotal]; linarith)
  obtain ⟨b, hbN, hb, hb'⟩ := exists_first_crossing w N
    (show 0 < 1 - κ / 4 by linarith)
    (show 1 - κ / 4 ≤ prefixMass w N by rw [htotal]; linarith)
  have hab : a < b := by
    by_contra h
    have hba : b ≤ a := by omega
    have hmono := prefixMass_mono hw hba
    have hsingle := hatom b hbN
    rw [prefixMass_succ] at hb'
    linarith
  exact ⟨a, b, hab, hbN, ha, ha', hb, hb', by linarith⟩

/-- The mass of a closed frequency interval. -/
noncomputable def intervalMass {ι : Type*} [Fintype ι] (w frequency : ι → ℝ)
    (a b : ℝ) : ℝ := by
  classical
  exact ∑ i, if a ≤ frequency i ∧ frequency i ≤ b then w i else 0

/-- The two closed halves cover the closed interval; midpoint atoms may be
counted twice, which has the favorable sign. -/
theorem intervalMass_le_halves {ι : Type*} [Fintype ι]
    (w frequency : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : ℝ) :
    intervalMass w frequency a b ≤ intervalMass w frequency a ((a + b) / 2) +
      intervalMass w frequency ((a + b) / 2) b := by
  classical
  unfold intervalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hcover : (a ≤ frequency i ∧ frequency i ≤ b) →
      (a ≤ frequency i ∧ frequency i ≤ (a + b) / 2) ∨
        ((a + b) / 2 ≤ frequency i ∧ frequency i ≤ b) := by
    intro hi
    rcases le_total (frequency i) ((a + b) / 2) with h | h
    · exact Or.inl ⟨hi.1, h⟩
    · exact Or.inr ⟨h, hi.2⟩
  split_ifs <;> first | linarith [hw i] | tauto

/-- One half of a frequency interval carries at least half its mass. -/
theorem exists_heavy_half {ι : Type*} [Fintype ι]
    (w frequency : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {a b m : ℝ}
    (hab : a ≤ b) (hm : m ≤ intervalMass w frequency a b) :
    ∃ e h : ℝ, a ≤ e ∧ e ≤ h ∧ h ≤ b ∧
      h - e = (b - a) / 2 ∧ m / 2 ≤ intervalMass w frequency e h := by
  have hs := intervalMass_le_halves w frequency hw a b
  by_cases hl : m / 2 ≤ intervalMass w frequency a ((a + b) / 2)
  · exact ⟨a, (a + b) / 2, le_rfl, by linarith, by linarith, by ring, hl⟩
  · exact ⟨(a + b) / 2, b, by linarith, by linarith, le_rfl, by ring,
      by linarith⟩

end LipschitzHilbert

end OAI
