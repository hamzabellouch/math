import OAI.NumberTheory.Jacobsthal.Analysis.WeightFutureIntegrals

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightDickmanComparison

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DerivativeWeights WeightFutureIntegrals

theorem deficits_le_gap {s : ℝ} (hs : 1 ≤ s) :
    lowerDeficit s ≤ gap s ∧ upperDeficit s ≤ gap s := by
  have h := deficit_sum s
  obtain ⟨ha, hc⟩ := deficits_pos hs
  constructor <;> linarith

theorem weights_dickman_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ s : ℝ, 2 ≤ s →
      (c * Dickman.rho (s - 2) ≤ phiEven s ∧ phiEven s ≤ C * Dickman.rho (s - 2)) ∧
      (c * Dickman.rho (s - 2) ≤ phiOdd s ∧ phiOdd s ≤ C * Dickman.rho (s - 2)) := by
  obtain ⟨δ, hδ, _, hcomp⟩ := deficits_uniform_comparison
  refine ⟨δ * sieveA, 3 * sieveA, mul_pos hδ sieveA_pos,
    mul_pos (by norm_num) sieveA_pos, ?_⟩
  intro s hs
  have hs1 : 1 ≤ s := by linarith
  have hp1 : 1 ≤ s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hg : 0 < gap (s - 1) := gap_pos hp1
  have hgprev : (s - 1) * gap (s - 1) = sieveA * Dickman.rho (s - 2) := by
    rw [gap_eq_rho hp1, show s - 1 - 1 = s - 2 by ring]
    field_simp
  have hgcur : s * gap s = sieveA * Dickman.rho (s - 1) := by
    rw [gap_eq_rho hs1]
    field_simp
  have hlow : (δ * sieveA) * Dickman.rho (s - 2) ≤ s * (δ * gap (s - 1)) := by
    calc
      _ = δ * ((s - 1) * gap (s - 1)) := by rw [hgprev]; ring
      _ = (s - 1) * (δ * gap (s - 1)) := by ring
      _ ≤ s * (δ * gap (s - 1)) := mul_le_mul_of_nonneg_right (by linarith) (mul_pos hδ hg).le
  have hlowE : s * (δ * gap (s - 1)) ≤ phiEven s := by
    rw [phiEven_eq_deficits hs]
    apply mul_le_mul_of_nonneg_left _ hs0.le
    have hc := (hcomp (s - 1) hp1).2.2.1
    have ha := (deficits_pos hs1).1
    linarith
  have hlowO : s * (δ * gap (s - 1)) ≤ phiOdd s := by
    rw [phiOdd_eq_deficits hs1]
    apply mul_le_mul_of_nonneg_left _ hs0.le
    have ha := (hcomp (s - 1) hp1).1
    have hc := (deficits_pos hs1).2
    linarith
  have huppE : phiEven s ≤ s * (gap s + gap (s - 1)) := by
    rw [phiEven_eq_deficits hs]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (deficits_le_gap hs1).1 (deficits_le_gap hp1).2) hs0.le
  have huppO : phiOdd s ≤ s * (gap s + gap (s - 1)) := by
    rw [phiOdd_eq_deficits hs1]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (deficits_le_gap hs1).2 (deficits_le_gap hp1).1) hs0.le
  have hupp : s * (gap s + gap (s - 1)) ≤ (3 * sieveA) * Dickman.rho (s - 2) := by
    have h1 : sieveA * Dickman.rho (s - 1) ≤ sieveA * Dickman.rho (s - 2) :=
      mul_le_mul_of_nonneg_left (Dickman.rho_antitone (by linarith)) sieveA_pos.le
    have h2 : s * gap (s - 1) ≤ 2 * ((s - 1) * gap (s - 1)) := by
      nlinarith [mul_le_mul_of_nonneg_right (show s ≤ 2 * (s - 1) by linarith) hg.le]
    rw [hgprev] at h2
    rw [mul_add, hgcur]
    nlinarith
  exact ⟨⟨le_trans hlow hlowE, le_trans huppE hupp⟩,
    ⟨le_trans hlow hlowO, le_trans huppO hupp⟩⟩

end NumberTheoryLean.WeightDickmanComparison

end

end Erdos970

end OAI
