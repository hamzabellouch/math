import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.NumberTheory.Ostmann.Characters.CharacterRoundedEndpoint

namespace OAI

/-! # The actual prime log indices fit the fixed-cell selection budget -/
namespace Ostmann
open Filter

noncomputable def characterIndexCutoff (β L : ℝ) : ℕ := ⌈Real.exp (β * L)⌉₊

theorem primeLogIndex_le_characterIndexCutoff (β L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : Real.log (Real.log (p : ℝ)) ≤ β * L) :
    primeLogIndex p ≤ characterIndexCutoff β L := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hh : Real.log (p : ℝ) ≤ Real.exp (β * L) :=
    (Real.log_le_iff_le_exp hlog).mp hbound
  have hindex : (primeLogIndex p : ℝ) ≤ characterIndexCutoff β L :=
    (primeLogIndex_bounds p hp).1.le.trans (hh.trans (Nat.le_ceil _))
  exact_mod_cast hindex

theorem eventual_character_index_cutoff (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, 5 * k ≤ characterIndexCutoff β L ∧
      ((characterIndexCutoff β L + 1 : ℕ) : ℝ) ≤ Real.exp ((β + 1) * L) := by
  have hlarge := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβ)).eventually
    (eventually_ge_atTop ((5 * k : ℕ) : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop (max 0 (Real.log 3))] with L hlarge hL
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have he : 1 ≤ Real.exp (β * L) := Real.one_le_exp (mul_nonneg hβ.le hL0)
  have hthree : 3 ≤ Real.exp L := by
    have hh := Real.exp_le_exp.mpr ((le_max_right _ _).trans hL)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using hh
  constructor
  · have hh := hlarge.trans (Nat.le_ceil (Real.exp (β * L)))
    exact_mod_cast hh
  · have hceil := Nat.ceil_lt_add_one (Real.exp_nonneg (β * L))
    change (characterIndexCutoff β L : ℝ) < Real.exp (β * L) + 1 at hceil
    rw [show (β + 1) * L = β * L + L by ring, Real.exp_add]
    push_cast
    nlinarith only [hceil, he, mul_le_mul_of_nonneg_left hthree (Real.exp_nonneg (β * L))]

end Ostmann

end OAI
