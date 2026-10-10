import OAI.NumberTheory.TwoPoint.Circuits.CircuitRandomRestriction

namespace OAI

/-! The spectral consequence of simplifying a Boolean function under random
restrictions: only restrictions whose decision trees remain deep contribute. -/

namespace TwoPointCorrelations

open scoped Classical

lemma restricted_error_le_degree_failure {n t : ℕ} (f : BooleanCube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (L : Finset (Fin n)) (y : BooleanCube n) :
    cubeAverage (fun x => (f (restrictCube L y x) -
      walshTruncation (fun z => f (restrictCube L y z)) t x) ^ 2) ≤
      if WalshDegreeLE (fun x => f (restrictCube L y x)) t then (0 : ℝ) else 1 := by
  split_ifs with h
  · rw [walshTruncation_error_eq_zero h]
  · apply (walshTruncation_error_le_square _ _).trans
    calc
      cubeAverage (fun x => (f (restrictCube L y x)) ^ 2) ≤
          cubeAverage (fun _ : BooleanCube n => (1 : ℝ)) := by
        apply cubeAverage_mono
        intro x
        rcases hf (restrictCube L y x) with hx | hx <;> simp [hx]
      _ = 1 := cubeAverage_const 1

theorem fourier_tail_le_degree_failure {n : ℕ} (f : BooleanCube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t d : ℕ)
    (ht : 2 * (t : ℝ) ≤ p * (d + 1)) (hd : 8 ≤ p * (d + 1)) :
    cubeAverage (fun x => (f x - walshTruncation f d x) ^ 2) ≤
      2 * (bernoulliCubeLaw n p hp hp1).average (fun mask => cubeAverage (fun y =>
        if WalshDegreeLE (fun x => f (restrictCube (sampledCoordinates mask) y x)) t
          then (0 : ℝ) else 1)) := by
  apply (fourier_tail_le_random_restriction f p hp hp1 t d ht hd).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply FiniteLaw.average_mono
  intro mask
  apply cubeAverage_mono
  intro y
  exact restricted_error_le_degree_failure f hf _ y

lemma degree_failure_le_decision_tree_failure {n t : ℕ} (f : BooleanCube n → ℝ) :
    (if WalshDegreeLE f t then (0 : ℝ) else 1) ≤
      if ∃ c : BooleanDecisionTree n, c.depth ≤ t ∧ c.indicator = f then 0 else 1 := by
  by_cases h : ∃ c : BooleanDecisionTree n, c.depth ≤ t ∧ c.indicator = f
  · obtain ⟨c, hc, rfl⟩ := h
    have hd := c.indicator_degree.mono hc
    simp only [hd, ite_true]
    split_ifs <;> norm_num
  · simp only [h, ite_false]
    split_ifs <;> norm_num

end TwoPointCorrelations

end OAI
