import OAI.NumberTheory.Ostmann.Construction.ConstituentAmplitudeEnergy

namespace OAI

/-! # Keeping the root frequency in the final counting measure -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def rootFibreSum {D R : Type*} [Fintype D]
    (root : D → R) (s : R) (F : D → ℂ) : ℂ :=
  ∑ d, if root d = s then F d else 0

theorem sum_rootFibreSum {D R : Type*} [Fintype D] [Fintype R]
    (root : D → R) (F : D → ℂ) :
    (∑ s, rootFibreSum root s F) = ∑ d, F d := by
  unfold rootFibreSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp

/-- Disjoint root fibres retain the same crude finite-frequency energy cost. -/
theorem rootFibreSum_energy {D R : Type*} [Fintype D] [Fintype R]
    (root : D → R) (F : D → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ d, ‖F d‖ ^ 2 ≤ E) :
    (∑ s, ‖rootFibreSum root s F‖ ^ 2) ≤ (Fintype.card D : ℝ) ^ 2 * E := by
  let c : R → ℝ := fun s => ((Finset.univ.filter fun d => root d = s).card : ℝ)
  have hc (s : R) : 0 ≤ c s := Nat.cast_nonneg _
  have hnorm (s : R) : ‖rootFibreSum root s F‖ ≤ c s * Real.sqrt E := by
    unfold rootFibreSum
    rw [← Finset.sum_filter]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ Finset.univ.filter (fun d => root d = s), Real.sqrt E :=
        Finset.sum_le_sum (fun d _ => Real.le_sqrt_of_sq_le (hF d))
      _ = _ := by simp [c]
  have hcount : ∑ s, c s = (Fintype.card D : ℝ) := by
    simp only [c, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
    rw [Finset.sum_comm]
    simp
  calc
    _ ≤ ∑ s, (c s * Real.sqrt E) ^ 2 :=
      Finset.sum_le_sum (fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hnorm s) 2)
    _ = (∑ s, c s ^ 2) * E := by
      simp only [mul_pow, Real.sq_sqrt hE, Finset.sum_mul]
    _ ≤ (∑ s, c s) ^ 2 * E :=
      mul_le_mul_of_nonneg_right (Finset.sum_sq_le_sq_sum_of_nonneg (fun s _ => hc s)) hE
    _ = _ := by rw [hcount]

/-- Expanding before taking norms leaves only equal-root pairs. -/
theorem rootFibreSum_pair {D K R : Type*} [Fintype D] [Fintype K] [Fintype R]
    (root : D → R) (root' : K → R) (F : D → ℂ) (G : K → ℂ) :
    (∑ s, rootFibreSum root s F * conj (rootFibreSum root' s G)) =
      ∑ d, ∑ k, if root d = root' k then F d * conj (G k) else 0 := by
  unfold rootFibreSum
  simp only [map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases h : root d = root' k
  · simp only [h, ite_true]
  · simp only [h, Ne.symm h, ite_false, map_zero, mul_zero]

theorem rootFibreSum_weighted_pair {D K R X : Type*}
    [Fintype D] [Fintype K] [Fintype R] [Fintype X]
    (root : D → R) (root' : K → R) (μ : X → ℝ)
    (F : D → X → ℂ) (G : K → X → ℂ) :
    (∑ s, ∑ x, (μ x : ℂ) *
      (rootFibreSum root s (fun d => F d x) * conj (rootFibreSum root' s (fun k => G k x)))) =
      ∑ d, ∑ k, if root d = root' k then ∑ x, (μ x : ℂ) * (F d x * conj (G k x)) else 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, rootFibreSum_pair, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : root d = root' k <;> simp only [h, ite_true, ite_false, mul_zero,
    Finset.sum_const_zero]

theorem rootFibreSum_pair_bound {D K R X : Type*}
    [Fintype D] [Fintype K] [Fintype R] [Fintype X]
    (root : D → R) (root' : K → R) (μ : X → ℝ)
    (F : D → X → ℂ) (G : K → X → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ d k, root d = root' k →
      ‖∑ x, (μ x : ℂ) * (F d x * conj (G k x))‖ ≤ E) :
    ‖∑ s, ∑ x, (μ x : ℂ) *
      (rootFibreSum root s (fun d => F d x) * conj (rootFibreSum root' s (fun k => G k x)))‖ ≤
        (Fintype.card D : ℝ) * Fintype.card K * E := by
  rw [rootFibreSum_weighted_pair]
  calc
    _ ≤ ∑ d, ∑ k, ‖if root d = root' k then
          ∑ x, (μ x : ℂ) * (F d x * conj (G k x)) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)
    _ ≤ ∑ _d : D, ∑ _k : K, E := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro k _
      by_cases h : root d = root' k
      · simpa only [h, ite_true] using hpair d k h
      · simpa only [h, ite_false, norm_zero] using hE
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Ostmann

end OAI
