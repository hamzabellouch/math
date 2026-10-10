import OAI.Analysis.LipschitzHilbert.Estimates.TerminalFlow

namespace OAI

/-! Transition conservation, telescoping path probabilities, and good-path amounts. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem transition_exit_conservation (p next : κ → ℝ) (T : κ → κ → ℝ)
    (node : ι → κ) (rate : ι → ℝ)
    (hnext : ∀ v, next v = ∑ u, p u * T u v)
    (hrow : ∀ u, (∑ v, T u v) + (∑ i, if node i = u then rate i else 0) = 1) :
    (∑ v, next v) + (∑ i, p (node i) * rate i) = ∑ u, p u := by
  classical
  have hexit : (∑ u, p u * ∑ i, if node i = u then rate i else 0) =
      ∑ i, p (node i) * rate i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_eq_single (node i)]
    · simp
    · intro u _ hu
      simp [Ne.symm hu]
    · simp
  calc
    _ = (∑ u, p u * ∑ v, T u v) + (∑ u, p u * ∑ i, if node i = u then rate i else 0) := by
      rw [hexit]
      congr 1
      simp_rw [hnext, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ u, p u * ((∑ v, T u v) + ∑ i, if node i = u then rate i else 0) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by simp_rw [hrow, mul_one]

theorem normalized_row_total (child : κ → ℝ) (amount : ι → ℝ) (node : ι → κ)
    (D : κ → ℝ) (u : κ) (hD : D u ≠ 0)
    (hden : D u = (∑ v, child v) + ∑ i, if node i = u then amount i else 0) :
    (∑ v, child v / D u) +
      (∑ i, if node i = u then amount i / D (node i) else 0) = 1 := by
  classical
  have hterm (i : ι) : (if node i = u then amount i / D (node i) else 0) =
      (if node i = u then amount i else 0) / D u := by
    by_cases hi : node i = u <;> simp [hi]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, ← hden, div_self hD]

omit [Fintype κ] [Fintype ι] in
theorem normalized_path_probability (V D p : ℕ → ℝ) (N : ℕ)
    (hV : V 0 ≠ 0) (hp0 : p 0 = 1)
    (hstep : ∀ j < N, p (j + 1) = p j * (V (j + 1) / D j)) :
    p N = (V N / V 0) * ∏ j ∈ Finset.range N, V j / D j := by
  induction N with
  | zero => simp [hp0, hV]
  | succ N ih =>
    rw [hstep N (by omega), ih (fun j hj => hstep j (by omega)), Finset.prod_range_succ]
    simp only [div_eq_mul_inv]
    ring

omit [Fintype κ] [Fintype ι] in
theorem terminal_probability_eq_path_amount (V D p : ℕ → ℝ) (N : ℕ) (a : ℝ)
    (hV : V 0 ≠ 0) (hp0 : p 0 = 1)
    (hstep : ∀ j < N, p (j + 1) = p j * (V (j + 1) / D j)) :
    p N * (a / D N) = (a * ∏ j ∈ Finset.range (N + 1), V j / D j) / V 0 := by
  rw [normalized_path_probability V D p N hV hp0 hstep, Finset.prod_range_succ]
  simp only [div_eq_mul_inv]
  ring

theorem good_path_amount_domination [DecidableEq ι] {N : ℕ} (F : TerminalFlow κ ι N)
    (bad : Finset ι) (V C : ℝ) (h e Q : ι → ℝ) (hV : 0 < V)
    (hQ : ∀ i, 0 ≤ Q i) (he : ∀ i, e i ≤ C * h i)
    (hprob : ∀ i, F.terminalProbability i = e i * Q i / V)
    (hrate : ∀ i, F.exitRate i ≤ C * h i) (hsmall : C * ∑ i ∈ bad, h i ≤ 1 / 2) :
    V ≤ 2 * C * ∑ i ∈ Finset.univ \ bad, h i * Q i := by
  have hhalf := F.good_terminal_probability_half bad h C hrate hsmall
  have hsum : (∑ i ∈ Finset.univ \ bad, F.terminalProbability i) =
      (∑ i ∈ Finset.univ \ bad, e i * Q i) / V := by
    simp_rw [hprob]
    rw [Finset.sum_div]
  rw [hsum] at hhalf
  have hamount := (le_div_iff₀ hV).mp hhalf
  have hcost : (∑ i ∈ Finset.univ \ bad, e i * Q i) ≤
      C * ∑ i ∈ Finset.univ \ bad, h i * Q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_right (he i) (hQ i)).trans_eq (mul_assoc _ _ _)
  linarith

end LipschitzHilbert

end

end OAI
