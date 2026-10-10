import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroFree
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.PrincipalHeightBound
import OAI.NumberTheory.Ostmann.Dirichlet.QuadraticZeroFreeSharp
import OAI.NumberTheory.Ostmann.Reuse.SiegelGap

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

theorem exists_primitive_log_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive → chi ≠ 1 →
      ∀ s : ℂ, 1 - c / modulusHeight q s.im ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cn, hcn, hnonquad⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cq, hcq, hquad⟩ := exists_primitive_quadratic_log_zero_free_region
  refine ⟨min cn cq, lt_min hcn hcq, ?_⟩
  intro q _ hq chi hprim hchi s hs
  have hH := modulusHeight_ge_one q s.im
  have hHp : 0 < modulusHeight q s.im := by linarith
  by_cases hsq : chi ^ 2 = 1
  · apply hquad q hq chi hprim hchi hsq s
    have h := div_le_div_of_nonneg_right (min_le_right cn cq) hHp.le
    linarith
  · apply hnonquad q chi hsq s
    have h := div_le_div_of_nonneg_right (min_le_left cn cq) hHp.le
    linarith

theorem exists_nonprincipal_log_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ s : ℂ, 1 - c / modulusHeight q s.im ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cp, hcp, hprimitive⟩ := exists_primitive_log_zero_free_region
  let c : ℝ := min cp (1 / 4)
  have hc : 0 < c := lt_min hcp (by norm_num)
  have hcc : c ≤ cp := min_le_left _ _
  have hc4 : c ≤ 1 / 4 := min_le_right _ _
  refine ⟨c, hc, ?_⟩
  intro q _ chi hchi s hs
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hH := modulusHeight_ge_one q s.im
  have hHp : 0 < modulusHeight q s.im := by linarith
  have hfrac : c / modulusHeight q s.im ≤ c := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have hrep : 0 < s.re := by linarith
  apply (LFunction_primitive_ne_zero_iff chi hchi hrep).mpr
  have hcond : chi.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hHm := modulusHeight_ge_one chi.conductor s.im
  have hmono := modulusHeight_mono hcond s.im
  have hfrac' : c / modulusHeight q s.im ≤ cp / modulusHeight chi.conductor s.im := by
    calc
      _ ≤ cp / modulusHeight q s.im := div_le_div_of_nonneg_right hcc hHp.le
      _ ≤ _ := div_le_div_of_nonneg_left hcp.le (by linarith) hmono
  apply hprimitive chi.conductor (conductor_ge_three chi hchi) chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive (primitiveCharacter_ne_one chi hchi) s
  linarith

theorem exists_height_one_log_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : ℕ), 3 ≤ Q → ∀ (q : ℕ) [NeZero q], q ≤ Q →
      ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → ∀ s : ℂ,
        |s.im| ≤ 1 → 1 - c / Real.log (Q : ℝ) ≤ s.re →
          DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨C, hC, hregion⟩ := exists_nonprincipal_log_zero_free_region
  refine ⟨C / 3, by positivity, ?_⟩
  intro Q hQ q _ hq chi hchi s ht hs
  have hQR : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  have hqlog : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by exact_mod_cast NeZero.pos q) (by exact_mod_cast hq)
  have hheight : Real.log (|s.im| + 6) ≤ 2 * Real.log (Q : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < |s.im| + 6)
      (show |s.im| + 6 ≤ (Q : ℝ) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hH := modulusHeight_ge_one q s.im
  have hHp : 0 < modulusHeight q s.im := by linarith
  have hbound : modulusHeight q s.im ≤ 3 * Real.log (Q : ℝ) := by
    unfold modulusHeight
    linarith
  have hwidth : (C / 3) / Real.log (Q : ℝ) ≤ C / modulusHeight q s.im := by
    calc
      _ = C / (3 * Real.log (Q : ℝ)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left hC.le hHp hbound
  exact hregion q chi hchi s (by linarith)

end Ostmann.Dirichlet

end OAI
