import OAI.NumberTheory.Ostmann.Characters.CharacterTargetWords
import OAI.NumberTheory.Ostmann.Construction.PrimeCellProductIntervals

namespace OAI

/-! # The selected target words as actual harmonic cells in the common prime space -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def CharacterTargetWord.cell {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T) (h : ℕ) :
    Finset ℕ := (loglogShell P (U + w.shell)).filter (fun p => primeLogIndex p = h)

theorem CharacterTargetWord.cell_subset {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T) (h : ℕ) :
    w.cell h ⊆ P :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

theorem CharacterTargetWord.cell_mass {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (h : ℕ) (hh : h ∈ w.indices) :
    δ * c / (32 * Real.exp (U + w.shell)) ≤ ∑ p ∈ w.cell h, (p : ℝ)⁻¹ :=
  (w.cells h hh).1

theorem CharacterTargetWord.cell_mean {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (h : ℕ) (hh : h ∈ w.indices) :
    δ / 2 ≤ (∑ p : P, (primeSubsetPrior P (w.cell h) p : ℂ) * F p).re := by
  rw [CharacterTargetWord.cell, primeSubsetPrior_cell_mean P (loglogShell P (U + w.shell)) (Finset.filter_subset _ _) h F]
  exact (w.cells h hh).2.2

theorem CharacterTargetWord.cell_prime_bounds {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (hP : ∀ p ∈ P, p.Prime) (h p : ℕ) (hp : p ∈ w.cell h) :
    primeCellLower h ≤ p ∧ p ≤ primeCellUpper h :=
  primeCell_interval p h (hP p (w.cell_subset h hp)) (Finset.mem_filter.mp hp).2

theorem CharacterTargetWord.cell_mass_exponential {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (hc : 0 < c) (hδ : 0 < δ) (β L : ℝ)
    (hU : U ≤ β * L) (hL : 5 * (k : ℝ) - Real.log (δ * c / 32) ≤ L)
    (h : ℕ) (hh : h ∈ w.indices) :
    Real.exp (-(β + 1) * L) ≤ ∑ p ∈ w.cell h, (p : ℝ)⁻¹ := by
  have hs : (w.shell : ℝ) ≤ 5 * k := by exact_mod_cast w.shell_le
  have he : Real.exp (-(β + 1) * L) ≤ δ * c / (32 * Real.exp (U + w.shell)) := by
    calc
      _ ≤ Real.exp (Real.log (δ * c / 32) - (U + w.shell)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hs, hU, hL])
      _ = _ := by
        rw [Real.exp_sub, Real.exp_log (by positivity)]
        ring
  exact he.trans (w.cell_mass h hh)

/-- This floor holds for every selected role and endpoint once the fixed
late-block width has been absorbed into L. -/
theorem eventual_character_target_cell_mass (c δ β : ℝ) (k : ℕ)
    (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ) (U T : ℝ),
      U ≤ β * L → ∀ (w : CharacterTargetWord P F c δ U k T) (h : ℕ),
      h ∈ w.indices → Real.exp (-(β + 1) * L) ≤ ∑ p ∈ w.cell h, (p : ℝ)⁻¹ := by
  filter_upwards [eventually_ge_atTop (5 * (k : ℝ) - Real.log (δ * c / 32))] with L hL
  intro P F U T hU w h hh
  exact w.cell_mass_exponential hc hδ β L hU hL h hh

end Ostmann

end OAI
