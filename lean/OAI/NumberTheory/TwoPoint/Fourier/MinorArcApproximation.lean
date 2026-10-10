import OAI.NumberTheory.TwoPoint.Fourier.MinorArcBilinearSieve
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace OAI

/-! A reduced rational approximation for the major/minor arc split. -/

namespace TwoPointCorrelations

lemma minor_arc_rational_approximation (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (r : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧ IsCoprime (q : ℤ) r ∧
      |α - (r : ℝ) / q| ≤ 1 / (((Q : ℝ) + 1) * q) ∧
      |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨a, ha, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  have hq0 : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have happrox : |α - (a.num : ℝ) / a.den| ≤ 1 / (((Q : ℝ) + 1) * a.den) := by
    simpa only [Rat.cast_def] using ha
  refine ⟨a.num, a.den, a.pos, hden, ?_, happrox, ?_⟩
  · apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using a.reduced.symm
  · apply happrox.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq0)
    have hden' : (a.den : ℝ) ≤ Q := by exact_mod_cast hden
    nlinarith

end TwoPointCorrelations

end OAI
