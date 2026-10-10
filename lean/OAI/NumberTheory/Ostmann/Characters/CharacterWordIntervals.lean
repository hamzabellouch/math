import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCenters
import OAI.NumberTheory.Ostmann.Construction.InitialWordAtomIntervals

namespace OAI

/-! # Integer word-bin endpoints have the same bounded errors as selected cells -/
namespace Ostmann
open scoped Classical

theorem initialWordAtomLower_word_gt_one {C : Type*} (j : ℕ) (hj : 0 < j)
    (lo : C → ℕ) (b : Bool) : 1 < initialWordAtomLower j lo (b, none) := by
  have he : (1 : ℝ) < Real.exp (j : ℝ) := Real.one_lt_exp_iff.mpr (by exact_mod_cast hj)
  have hh := he.trans_le (Nat.le_ceil (Real.exp (j : ℝ)))
  change 1 < ⌈Real.exp (j : ℝ)⌉₊
  exact_mod_cast hh

theorem character_word_interval_errors {k : ℕ} (j : ℕ) (c : ℝ) (hc : 1 ≤ c)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ) (F : ℝ)
    (lo hi : CharacterCell k → ℕ)
    (hlo : ∀ v, Real.exp (characterLogCenter j T a F (true, some v) - c) ≤ lo v)
    (hhi : ∀ v, (hi v : ℝ) ≤ Real.exp (characterLogCenter j T a F (true, some v) + c)) :
    (∀ v, Real.exp (characterLogCenter j T a F v - c) ≤ initialWordAtomLower j lo v) ∧
    ∀ v, (initialWordAtomUpper j hi v : ℝ) ≤ Real.exp (characterLogCenter j T a F v + c) := by
  constructor
  · rintro ⟨b, v⟩
    cases v with
    | none =>
      change Real.exp ((j : ℝ) - c) ≤ (⌈Real.exp (j : ℝ)⌉₊ : ℝ)
      exact (Real.exp_le_exp.mpr (by linarith)).trans (Nat.le_ceil _)
    | some v => exact hlo v
  · rintro ⟨b, v⟩
    cases v with
    | none =>
      change ((⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) : ℝ) ≤ Real.exp ((j : ℝ) + c)
      have hp : 1 ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ :=
        Nat.ceil_pos.mpr (Real.exp_pos _)
      rw [Nat.cast_sub hp, Nat.cast_one]
      have hh := Nat.ceil_lt_add_one (Real.exp_pos ((j : ℝ) + 1)).le
      apply le_trans (by linarith : (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) - 1 ≤
        Real.exp ((j : ℝ) + 1))
      exact Real.exp_le_exp.mpr (by linarith)
    | some v => exact hhi v

end Ostmann

end OAI
