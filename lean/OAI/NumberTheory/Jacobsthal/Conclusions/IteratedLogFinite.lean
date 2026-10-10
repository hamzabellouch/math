import OAI.NumberTheory.Jacobsthal.Conclusions.IteratedLogScales
import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalFinite

namespace OAI

namespace Erdos970.NumberTheoryLean.IteratedLogFinite

open _root_.Filter IteratedLogScales
open scoped BigOperators Topology

/-- Absorb the bounded range without changing any interval quantifier. -/
theorem of_eventually
    (hlarge : ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ m : ℕ, Targets.IsJacobsthalBound k m ∧
        (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (loglog k) ^ 2) :
    Targets.JacobsthalIteratedLog := by
  obtain ⟨C, hC, hlarge⟩ := hlarge
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlarge
  let weight : ℕ → ℝ := fun k =>
    (((k + 1) * (k + 1).factorial : ℕ) : ℝ) * (loglog k) ^ 2
  let D : ℝ := C + ∑ k ∈ Finset.range K, weight k
  have hw (k : ℕ) : 0 ≤ weight k := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hCD : C ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hw k)
  have hD : 0 < D := hC.trans_le hCD
  refine ⟨D, hD, ?_⟩
  intro k hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (loglog k) ^ 2 := sq_pos_of_pos (loglog_pos hkR)
  by_cases hKk : K ≤ k
  · obtain ⟨m, hm, hb⟩ := hK k hKk
    refine ⟨m, hm, hb.trans ?_⟩
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (sq_nonneg _)) hden.le
  · refine ⟨(k + 1) * (k + 1).factorial,
      JacobsthalFinite.factorial_isJacobsthalBound k, ?_⟩
    apply (le_div_iff₀ hden).mpr
    have hsum : weight k ≤ ∑ i ∈ Finset.range K, weight i :=
      Finset.single_le_sum (fun i _ => hw i) (Finset.mem_range.mpr (by omega))
    have hweight : weight k ≤ D := hsum.trans (by dsimp [D]; linarith)
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    exact hweight.trans (by nlinarith)

end Erdos970.NumberTheoryLean.IteratedLogFinite

end OAI
