import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaStripBound

namespace OAI

/-! # A factorial bound for Gamma on expanding right-half-plane disks -/

namespace Ostmann

open Complex

theorem gamma_factorial_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (s : ℂ), (1 / 4 : ℝ) ≤ s.re → s.re ≤ (N : ℝ) + 2 →
      ‖Complex.Gamma s‖ ≤ C + ((N + 1).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := gamma_positive_strip_bound (1 / 4) 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N s hs hs'
  by_cases hsmall : s.re ≤ 2
  · exact (hbound s hs hsmall).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · have hpos : 0 < s.re := by linarith
    have hm : Real.Gamma s.re ≤ Real.Gamma ((N : ℝ) + 2) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by change 2 ≤ s.re; linarith)
        (by change 2 ≤ (N : ℝ) + 2; linarith [Nat.cast_nonneg (α := ℝ) N]) hs'
    have he : Real.Gamma ((N : ℝ) + 2) = ((N + 1).factorial : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        Real.Gamma_nat_eq_factorial (N + 1)
    calc
      _ ≤ Real.Gamma s.re := gamma_norm_le_real s hpos
      _ ≤ Real.Gamma ((N : ℝ) + 2) := hm
      _ = _ := he
      _ ≤ _ := le_add_of_nonneg_left hC.le

end Ostmann

end OAI
