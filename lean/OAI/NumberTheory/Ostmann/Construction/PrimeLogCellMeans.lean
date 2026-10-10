import OAI.NumberTheory.Ostmann.Construction.FiniteCellMeans
import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellUpper
import OAI.NumberTheory.Ostmann.Construction.PrimeLogGrid

namespace OAI

/-! # Actual prime log cells and their means -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- The cell `(h,h+1]` containing the logarithm of a prime. -/
noncomputable def primeLogIndex (p : ℕ) : ℕ := ⌈Real.log (p : ℝ)⌉₊ - 1

theorem primeLogIndex_bounds (p : ℕ) (hp : p.Prime) :
    (primeLogIndex p : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (primeLogIndex p : ℝ) + 1 := by
  have hx : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  let n := ⌈Real.log (p : ℝ)⌉₊
  have hn : 0 < n := by
    have h := Nat.le_ceil (Real.log (p : ℝ))
    by_contra! hz
    have he : n = 0 := Nat.eq_zero_of_le_zero hz
    change Real.log (p : ℝ) ≤ (n : ℝ) at h
    rw [he, Nat.cast_zero] at h
    linarith
  have heq : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
  have hu := Nat.le_ceil (Real.log (p : ℝ))
  have hl := Nat.ceil_lt_add_one hx.le
  change (n : ℝ) < Real.log (p : ℝ) + 1 at hl
  change Real.log (p : ℝ) ≤ (n : ℝ) at hu
  change ((n - 1 : ℕ) : ℝ) < Real.log (p : ℝ) ∧
    Real.log (p : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + 1
  constructor <;> linarith

theorem primeLogIndex_cell (p : ℕ) (hp : p.Prime) :
    p ∈ primeLogCellSet 1 0 (primeLogIndex p) ((primeLogIndex p : ℝ) + 1) := by
  apply mem_primeLogCellSet_iff.mpr
  exact ⟨hp, by simp [Nat.ModEq, Nat.mod_one], primeLogIndex_bounds p hp⟩

/-- The actual prime fibers obey the uniform cell cap used in good-cell
selection. -/
theorem PublishedProgressionInput.primeLogIndex_mass_bound (P0 : PublishedProgressionInput) :
    ∀ᶠ B : ℝ in atTop, ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ h : ℕ, B ≤ h →
      finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ≤ 2 / B := by
  obtain ⟨S, hS⟩ := eventually_atTop.mp P0.prime_log_cell_upper
  filter_upwards [eventually_ge_atTop (max S 1)] with B hB P hP h hh
  have hpos : 0 < B := lt_of_lt_of_le (by norm_num) ((le_max_right S 1).trans hB)
  have hbound := hS (h : ℝ) ((le_max_left S 1).trans (hB.trans hh))
    (P.filter (fun p => primeLogIndex p = h)) (by
      intro p hp
      obtain ⟨hpP, hpH⟩ := Finset.mem_filter.mp hp
      simpa only [hpH] using primeLogIndex_cell p (hP p hpP))
  apply hbound.trans
  exact div_le_div_of_nonneg_left (by norm_num) hpos hh

end Ostmann

end OAI
