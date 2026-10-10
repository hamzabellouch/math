import Mathlib

namespace OAI

namespace MetricKMedian

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
noncomputable def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω
noncomputable def prob (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  μ.expect (fun ω => if E ω then 1 else 0)

theorem expect_mono (μ : FiniteLaw Ω) {f h : Ω → ℝ} (hfh : ∀ ω, f ω ≤ h ω) :
    μ.expect f ≤ μ.expect h := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfh ω) (μ.nonneg ω))

theorem expect_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))

theorem expect_const (μ : FiniteLaw Ω) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.total, one_mul]

theorem expect_add (μ : FiniteLaw Ω) (f h : Ω → ℝ) :
    μ.expect (fun ω => f ω + h ω) = μ.expect f + μ.expect h := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw Ω) (f h : Ω → ℝ) :
    μ.expect (fun ω => f ω - h ω) = μ.expect f - μ.expect h := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => c * f ω) = c * μ.expect f := by
  simp only [expect, ← Finset.mul_sum, mul_left_comm]

theorem expect_mul_right (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω * c) = μ.expect f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

theorem expect_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I) (f : Ω → I → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f ω i) = ∑ i ∈ s, μ.expect (fun ω => f ω i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : 0 ≤ μ.prob E := by
  apply μ.expect_nonneg
  intro ω
  split_ifs <;> norm_num

theorem prob_le_one (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : μ.prob E ≤ 1 := by
  calc
    μ.prob E ≤ μ.expect (fun _ => 1) := μ.expect_mono (fun ω => by split_ifs <;> norm_num)
    _ = 1 := μ.expect_const _

theorem prob_mono (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) : μ.prob E ≤ μ.prob F := by
  apply μ.expect_mono
  intro ω
  split_ifs with he hf hf <;> try norm_num
  exact False.elim (hf (hEF ω he))

theorem prob_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω ↔ F ω) : μ.prob E = μ.prob F := by
  exact le_antisymm (μ.prob_mono fun ω => (hEF ω).mp) (μ.prob_mono fun ω => (hEF ω).mpr)

theorem prob_exists_le_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I)
    (E : I → Ω → Prop) [∀ i, DecidablePred (E i)] :
    μ.prob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  unfold prob
  rw [← expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, E i ω
  · obtain ⟨i, hi, hei⟩ := h
    simp only [ite_eq_left (show ∃ i ∈ s, E i ω from ⟨i, hi, hei⟩)]
    have hsingle := Finset.single_le_sum (f := fun j => if E j ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) hi
    simpa only [ite_eq_left hei] using hsingle
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end FiniteLaw

namespace BatchRemainder

theorem pointwise {E : Type*} [DecidableEq E] (A : Finset E)
    (b : E → ℝ) {D K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ e ∈ A, -K ≤ b e) (hD : D ≤ K)
    (hzero : A = ∅ → D ≤ 0) (hone : ∀ e, A = {e} → D ≤ b e) :
    D ≤ (∑ e ∈ A, b e) + 2 * K * (A.offDiag.card : ℝ) := by
  rcases lt_or_ge A.card 2 with hsmall | hlarge
  · have hc : A.card ≤ 1 := by omega
    by_cases h : A = ∅
    · simpa only [h, Finset.sum_empty, Finset.offDiag_empty, Finset.card_empty,
        Nat.cast_zero, mul_zero, add_zero] using hzero h
    · have hpos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
      obtain ⟨e, ha⟩ := Finset.card_eq_one.mp (show A.card = 1 by omega)
      simpa only [ha, Finset.sum_singleton, Finset.offDiag_singleton,
        Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] using hone e ha
  · have hsum := Finset.sum_le_sum hb
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hn : (2:ℝ) ≤ A.card := by exact_mod_cast hlarge
    have hcard : (A.offDiag.card : ℝ) = (A.card : ℝ) * ((A.card : ℝ) - 1) := by
      rw [Finset.offDiag_card]
      have hrewrite : A.card * A.card - A.card = A.card * (A.card - 1) := by
        simp only [Nat.mul_sub_left_distrib, mul_one]
      rw [hrewrite, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard]
    have hquad : (A.card : ℝ) + 1 ≤ 2 * (A.card : ℝ) * ((A.card : ℝ) - 1) := by
      nlinarith only [hn, sq_nonneg ((A.card : ℝ) - 2)]
    have hmul := mul_le_mul_of_nonneg_left hquad hK
    nlinarith only [hsum, hD, hmul]

theorem expect_selected_sum {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) :
    μ.expect (fun ω => ∑ e ∈ A ω, b e) =
      ∑ e, μ.prob (fun ω => e ∈ A ω) * b e := by
  have hsum : ∀ ω, (∑ e ∈ A ω, b e) = ∑ e, (if e ∈ A ω then (1:ℝ) else 0) * b e := by
    intro ω
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    simp only [Finset.filter_univ_mem]
  simp_rw [hsum, FiniteLaw.expect_sum, FiniteLaw.expect_mul_right]
  rfl

theorem expect_pair_count {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) :
    μ.expect (fun ω => (Finset.card (A ω).offDiag : ℝ)) =
      ∑ p ∈ (Finset.univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
  have hset : ∀ ω, (A ω).offDiag =
      (Finset.univ : Finset E).offDiag.filter (fun p => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
    intro ω
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hsum : ∀ ω, (Finset.card (A ω).offDiag : ℝ) =
      ∑ p ∈ (Finset.univ : Finset E).offDiag, if p.1 ∈ A ω ∧ p.2 ∈ A ω then (1:ℝ) else 0 := by
    intro ω
    rw [hset, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hsum, FiniteLaw.expect_sum]
  rfl

theorem expectation_le {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) (D : Ω → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ e, -K ≤ b e) (hD : ∀ ω, D ω ≤ K)
    (hzero : ∀ ω, A ω = ∅ → D ω ≤ 0)
    (hone : ∀ ω e, A ω = {e} → D ω ≤ b e) :
    μ.expect D ≤ (∑ e, μ.prob (fun ω => e ∈ A ω) * b e) +
      2 * K * ∑ p ∈ (Finset.univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
  have h := μ.expect_mono (fun ω => pointwise (A ω) b hK (fun e _ => hb e)
    (hD ω) (hzero ω) (hone ω))
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul,
    expect_selected_sum, expect_pair_count] at h
  exact h

end BatchRemainder
end MetricKMedian

end OAI
