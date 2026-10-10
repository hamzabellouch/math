import OAI.NumberTheory.Ostmann.Construction.InitialWordCoordinates
import OAI.NumberTheory.Ostmann.Construction.InitialAtomGuards
import OAI.NumberTheory.Ostmann.Construction.WordProductWindow

namespace OAI

/-! # Exact closed integer ranges for the original logarithmic word bins -/

namespace Ostmann
open scoped BigOperators Classical

/-- Integer endpoints express the half-open logarithmic bin exactly. -/
theorem floor_log_eq_iff_integer_range (M j : ℕ) (hM : 0 < M) :
    ⌊Real.log (M : ℝ)⌋₊ = j ↔
      (M : ℝ) ∈ Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ)
        (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  rw [Nat.floor_eq_iff hlog]
  have hlo : (j : ℝ) ≤ Real.log (M : ℝ) ↔ ⌈Real.exp (j : ℝ)⌉₊ ≤ M := by
    rw [Nat.ceil_le]
    rw [← Real.exp_le_exp, Real.exp_log hm]
  have hhi : Real.log (M : ℝ) < (j : ℝ) + 1 ↔
      M ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 := by
    rw [Real.log_lt_iff_lt_exp hm, ← Nat.lt_ceil]
    have hc : 0 < ⌈Real.exp ((j : ℝ) + 1)⌉₊ := by
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    omega
  simpa only [Set.mem_Icc, Nat.cast_le] using and_congr hlo hhi

noncomputable def initialWordBinRange {C : Type*} (role : Bool × Option C → CopyScheduleRole)
    (b : Bool) (j : ℕ) : ScheduleAtomRange role 0 where
  atoms := [⟨(b, none), trivial⟩]
  lower := ⌈Real.exp (j : ℝ)⌉₊
  upper := (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)

theorem initialWordBinRange_holds {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (k : ℕ) (s : C → ℕ)
    (b : Bool) (j : ℕ)
    (x : (Σ a : Bool × Option C, Fin (initialWordSize k s a.2)) → ℕ)
    (hx : 0 < ∏ i : Fin k, x ⟨(b, none), i⟩) :
    (initialWordBinRange role b j).Holds (fun a => ∏ i, x ⟨a.val, i⟩) ↔
      ⌊Real.log ((∏ i : Fin k, x ⟨(b, none), i⟩ : ℕ) : ℝ)⌋₊ = j := by
  simp only [initialWordBinRange, ScheduleAtomRange.Holds, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  change ((∏ i : Fin k, x ⟨(b, none), i⟩ : ℕ) : ℝ) ∈
    Set.Icc (⌈Real.exp (j : ℝ)⌉₊ : ℝ) (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) ↔ _
  exact (floor_log_eq_iff_integer_range _ j hx).symm

theorem wordLogBin_eq_iff_integer_range {m : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (τ : ℝ) (w : Fin (m + 1) → P)
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hhi : (∑ i, Real.log (w i : ℝ)) ≤ 4 * τ) :
    wordLogBin τ (fun i => Real.log (w i : ℝ)) = b ↔
      ((∏ i, (w i : ℕ) : ℕ) : ℝ) ∈
        Set.Icc (⌈Real.exp (b.val : ℝ)⌉₊ : ℝ)
          (⌈Real.exp ((b.val : ℝ) + 1)⌉₊ - 1 : ℕ) := by
  rw [Fin.ext_iff, wordLogBin_val τ _ hhi]
  have hp : 0 < ∏ i, (w i : ℕ) := Finset.prod_pos (fun i _ => (hP _ (w i).property).pos)
  have he : Real.log ((∏ i, (w i : ℕ) : ℕ) : ℝ) = ∑ i, Real.log (w i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun i _ => by
      exact_mod_cast (hP _ (w i).property).ne_zero)]
  rw [← he]
  exact floor_log_eq_iff_integer_range _ _ hp

end Ostmann

end OAI
