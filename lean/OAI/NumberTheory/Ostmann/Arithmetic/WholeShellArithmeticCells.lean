import OAI.NumberTheory.Ostmann.Arithmetic.WholeShellGeometry
import OAI.NumberTheory.Ostmann.Construction.WholeShellMass
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProgressionCutoff

namespace OAI

/-! # The numerical and measure data of the full bulk-shell partition -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem whole_shell_arithmetic_cells (C Cmass : ℝ) (hM : MertensEstimate C)
    (hCmass : 1 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop, ∀ (M : ℕ) [NeZero M], M ≤ bulkProgressionCutoff L →
      let a := (4 / 1000 : ℝ) * L
      let b := (6 / 1000 : ℝ) * L
      (Fintype.card (Fin (wholePrimeGridCount b)) : ℝ) ≤
        Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) ∧
      (∀ c, 1 ≤ wholeShellLower a b c) ∧
      (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ wholeShellLower a b c) ∧
      (∀ c, wholeShellLower a b c ≤ wholeShellUpper a b c) ∧
      (∀ c, wholeShellUpper a b c ≤ wholeShellLower a b c + 1) ∧
      (∀ c d, c ≠ d → wholeShellUpper a b c ≤ wholeShellLower a b d ∨
        wholeShellUpper a b d ≤ wholeShellLower a b c) ∧
      (∀ c, (M : ℝ) ≤ Real.exp (wholeShellLower a b c)) ∧
      primeCellSupport M (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
        (fun c => wholeShellLower a b c.1) (fun c => wholeShellUpper a b c.1) =
        primeLogCellSet 1 0 (Real.exp a) (Real.exp b) ∧
      Real.exp (-Cmass * L) ≤ ∑ q ∈ primeLogCellSet 1 0 (Real.exp a) (Real.exp b), (q : ℝ)⁻¹ := by
  have hlarge := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 1000))).eventually
      (eventually_ge_atTop (2 * (Real.log 2 + 2 * C)))
  filter_upwards [wholePrimeGridCount_eventual (6 / 1000) (by norm_num), hlarge,
    eventually_ge_atTop (max 0 (max (Real.log 4) (500 * Real.log 2)))]
    with L hgrid hlarge hL
  intro M _ hMQ
  dsimp only
  let a : ℝ := (4 / 1000) * L
  let b : ℝ := (6 / 1000) * L
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hL4 : Real.log 4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 500 * Real.log 2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hab : a ≤ b := by dsimp only [a, b]; linarith only [hL0]
  have hgeometry := whole_shell_geometry a b hab
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num) hL0
  have hMbase : (M : ℝ) ≤ Real.exp (Real.exp a) :=
    modulus_le_exp_bulk_endpoint hMQ hL0
      (Real.exp_le_exp.mpr (by dsimp only [a]; linarith only [hL0]))
  refine ⟨?_, ?_, ?_, hgeometry.2.1, hgeometry.2.2.1, hgeometry.2.2.2, ?_,
    whole_shell_support M a b hab hMbase, ?_⟩
  · simpa only [Fintype.card_fin] using hgrid b (le_refl _)
  · intro c
    exact (Real.one_le_exp_iff.mpr ha0).trans (hgeometry.1 c)
  · intro c
    exact (Real.exp_le_exp.mpr (by dsimp only [a]; linarith only [hL0])).trans (hgeometry.1 c)
  · intro c
    exact hMbase.trans (Real.exp_le_exp.mpr (hgeometry.1 c))
  · have htwo : 2 * Real.exp a ≤ Real.exp b := by
      have he : Real.log 2 + a ≤ b := by dsimp only [a, b]; linarith only [hL2]
      have hh := Real.exp_le_exp.mpr he
      simpa only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh
    have he : Real.exp (-Cmass * L) ≤ (1 / 4 : ℝ) := by
      have hprod := mul_le_mul_of_nonneg_right hCmass hL0
      calc
        _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by nlinarith only [hprod, hL4])
        _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num
    exact he.trans (whole_shell_mass_lower hM (Real.exp a) (Real.exp b)
      (Real.one_le_exp_iff.mpr ha0) hlarge htwo)

end Ostmann

end OAI
