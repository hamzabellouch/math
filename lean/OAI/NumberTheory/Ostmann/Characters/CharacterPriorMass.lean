import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.NumberTheory.Ostmann.Characters.CharacterFullPrimeCells
import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCellData

namespace OAI

/-! # Harmonic mass floors for every original signed character marginal -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The bulk has linear mass, the top shell has fixed positive mass, and all
remaining selected cells already have the proved exponential mass floor. -/
theorem eventual_full_character_mass_floor (a b C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∀ (k m : ℕ) (r : Fin k → ℕ) (f : ℕ)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ →
      (∀ i : Fin m, a * L ≤ ∑ p ∈ Q i.succ, (p : ℝ)⁻¹) →
      (∀ v i, Real.exp (-C * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      ∀ i, Real.exp (-C * L) ≤
        ∑ p ∈ characterFullPrimeCells m r f Q R i, (p : ℝ)⁻¹ := by
  have he : ∀ᶠ L : ℝ in atTop, Real.exp (-C * L) ≤ min a b :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hC)).eventually_le_const (lt_min ha hb)).mono (by
        intro L hL
        simpa only [Function.comp_apply, id_eq, neg_mul] using hL)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with L he hL
  intro k m r f Q R htop hbulk hrest
  have hword (i : Fin (m + 1)) : Real.exp (-C * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (he.trans (min_le_right _ _)).trans htop
    · have hh : a ≤ a * L := by nlinarith only [ha, hL]
      exact ((he.trans (min_le_left _ _)).trans hh).trans (hbulk j)
  rintro ⟨⟨sgn, v⟩, i⟩
  cases v with
  | none => exact hword i
  | some v => exact hrest v i

theorem harmonic_mass_inv_le_exp (Q : Finset ℕ) (C L : ℝ)
    (hQ : Real.exp (-C * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) :
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * L) := by
  have h := inv_anti₀ (Real.exp_pos (-C * L)) hQ
  simpa only [← Real.exp_neg, neg_mul, neg_neg] using h

theorem harmonic_mass_inv_energy_budget (Q : Finset ℕ) (C L M : ℝ)
    (hC : 0 ≤ C) (hLM : L ≤ M)
    (hQ : Real.exp (-C * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) :
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * (1 + M)) := by
  apply (harmonic_mass_inv_le_exp Q C L hQ).trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hC)

end Ostmann

end OAI
