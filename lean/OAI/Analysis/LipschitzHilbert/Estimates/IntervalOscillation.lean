import OAI.Analysis.LipschitzHilbert.Estimates.VariationIntervals

namespace OAI

/-! Actual maxima of subinterval sums on residual segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def intervalOscillation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0)

theorem intervalOscillation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) : 0 ≤ intervalOscillation F N a b := by
  classical
  apply Finset.le_sup'_of_le (b := ((0 : Fin (N + 1)), (0 : Fin (N + 1))))
    (f := fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ _)
  split_ifs <;> positivity

theorem exists_intervalOscillation_eq {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) :
    ∃ c d : ℕ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ intervalOscillation F N a b = ‖F d - F c‖ := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0)
  change intervalOscillation F N a b = _ at hq
  by_cases h : a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b
  · rw [ite_eq_left h] at hq
    exact ⟨q.1, q.2, h.1, h.2.1, h.2.2, hq⟩
  · rw [ite_eq_right h] at hq
    exact ⟨a, a, le_rfl, le_rfl, hab, by simpa only [sub_self, norm_zero] using hq⟩

theorem increment_le_intervalOscillation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ N) :
    ‖F d - F c‖ ≤ intervalOscillation F N a b := by
  classical
  let q : Fin (N + 1) × Fin (N + 1) :=
    (⟨c, by omega⟩, ⟨d, by omega⟩)
  have h := Finset.le_sup'
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ q)
  simpa only [intervalOscillation, q,
    ite_eq_left (show a ≤ c ∧ c ≤ d ∧ d ≤ b from ⟨hac, hcd, hdb⟩)] using h

/-- Choose an actual maximizing subinterval in every disjoint segment,
then use one common variation bound for all segments together. -/
theorem intervalOscillation_cube_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N S : ℕ) (a b : Fin S → ℕ) (hS : S ≤ N)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    (∑ i, intervalOscillation F N (a i) (b i) ^ 3) ≤
      finiteCubicVariation (fun n => F (min n N)) (2 * N) := by
  choose c d hac hcd hdb heq using fun i =>
    exists_intervalOscillation_eq F N (a i) (b i) (hab i)
  simp_rw [heq]
  exact ordered_intervals_le_variation F N S c d hS hcd
    (fun i => (hdb i).trans (hb i))
    (fun i j hij => (hdb i).trans ((horder i j hij).trans (hac j)))

end LipschitzHilbert

end

end OAI
