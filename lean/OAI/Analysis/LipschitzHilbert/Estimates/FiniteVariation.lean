import OAI.Analysis.LipschitzHilbert.Estimates.PublishedInputs
import OAI.Analysis.LipschitzHilbert.Estimates.MixedNorms

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

theorem scalar_finiteCubicVariation {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) = variationCube F N x := by
  classical
  have heq (p : Fin (N + 1) → Fin (N + 1)) :
      ENNReal.ofReal (if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) =
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0 := by
    split_ifs
    · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · exact ENNReal.ofReal_zero
  apply le_antisymm
  · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0)
    change ENNReal.ofReal (Finset.univ.sup' _ _) ≤ _
    rw [hp, heq]
    change (if Monotone p then ∑ i : Fin N,
      ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0) ≤
      Finset.univ.sup _
    exact Finset.le_sup (f := fun q : Fin (N + 1) → Fin (N + 1) =>
      if Monotone q then ∑ i : Fin N,
        ‖F (q i.succ) x - F (q i.castSucc) x‖ₑ ^ 3 else 0) (Finset.mem_univ p)
  · apply Finset.sup_le
    intro p _
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    exact Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N,
        ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) (Finset.mem_univ p)

/-- Minkowski in `ℓ^(3/2)` moves the Euclidean coordinates outside the
variation. The constant does not depend on the number of coordinates. -/
theorem euclidean_partition_variation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℝ κ) (N : ℕ)
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

theorem euclidean_finiteCubicVariation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℝ κ) (N : ℕ) :
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
    apply (euclidean_partition_variation_le F N p).trans
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
