import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation

namespace OAI

/-! Dimension-independent variation comparison for complex coordinates. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem complex_partition_variation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ)
    (p : Fin (N + 1) → Fin (N + 1)) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (2 / 3 : ℝ) ≤
      ∑ k, (∑ i : Fin N,
        ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 3) ^ (2 / 3 : ℝ) := by
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have h := PhaseCombinatorics.finite_minkowski
    (fun k (i : Fin N) => ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num only [one_div_div, div_one] at h
  have hsum (i : Fin N) :
      (∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2) ^ (3 / 2 : ℝ) =
      ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 := by
    have heq : ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 =
        ∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [← heq]
    exact hpow _ (norm_nonneg _)
  simpa only [hsum, hpow _ (norm_nonneg _)] using h

theorem complex_finiteCubicVariation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, (finiteCubicVariation (fun n => F n k) N) ^ (2 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    apply (complex_partition_variation_le F N p).trans
    apply Finset.sum_le_sum
    intro k _
    exact Real.rpow_le_rpow (by positivity)
      (partition_le_finiteCubicVariation (fun n => F n k) N p hmono) (by norm_num)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    exact Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _


end LipschitzHilbert

end

end OAI
