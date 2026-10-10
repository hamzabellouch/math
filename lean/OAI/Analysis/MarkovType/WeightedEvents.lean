import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {Ω : Type*} [Fintype Ω]

noncomputable def eventMass (μ : Ω → ℝ) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then μ ω else 0

noncomputable def weightedMean (μ X : Ω → ℝ) : ℝ := ∑ ω, μ ω * X ω

theorem eventMass_nonneg (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (A : Ω → Prop) : 0 ≤ eventMass μ A := by
  classical
  unfold eventMass
  apply Finset.sum_nonneg
  intro ω _
  by_cases hA : A ω
  · simpa only [ite_eq_left hA] using hμ ω
  · simp only [ite_eq_right hA, le_refl]

theorem eventMass_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) :
    eventMass μ A ≤ eventMass μ B := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp only [ite_eq_left hA, ite_eq_left (hAB ω hA), le_refl]
  · rw [ite_eq_right hA]
    by_cases hB : B ω
    · simpa only [ite_eq_left hB] using hμ ω
    · simp only [ite_eq_right hB, le_refl]

theorem eventMass_exists_le_sum {ι : Type*} [Fintype ι]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (bad : ι → Ω → Prop) :
    eventMass μ (fun ω => ∃ i, bad i ω) ≤ ∑ i, eventMass μ (bad i) := by
  classical
  unfold eventMass
  calc
    _ ≤
        ∑ ω, ∑ i, if bad i ω then μ ω else 0 := by
      apply Finset.sum_le_sum
      intro ω _
      have hnonneg : ∀ i : ι, 0 ≤ (if bad i ω then μ ω else 0) := by
        intro i
        by_cases hi : bad i ω
        · simpa only [ite_eq_left hi] using hμ ω
        · simp only [ite_eq_right hi, le_refl]
      by_cases hbad : ∃ i, bad i ω
      · rw [ite_eq_left hbad]
        obtain ⟨i, hi⟩ := hbad
        calc
          μ ω = (if bad i ω then μ ω else 0) := by simp only [ite_eq_left hi]
          _ ≤ ∑ j, if bad j ω then μ ω else 0 :=
            Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      · rw [ite_eq_right hbad]
        exact Finset.sum_nonneg (fun i _ => hnonneg i)
    _ = ∑ i, ∑ ω, if bad i ω then μ ω else 0 := Finset.sum_comm

theorem eventMass_sub_le_and_not (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (A B : Ω → Prop) :
    eventMass μ A - eventMass μ B ≤ eventMass μ (fun ω => A ω ∧ ¬ B ω) := by
  classical
  have hcover : eventMass μ A ≤
      eventMass μ (fun ω => A ω ∧ ¬ B ω) + eventMass μ B := by
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hA : A ω <;> by_cases hB : B ω
    · simp only [hA, hB, not_true_eq_false, and_false, ite_false, ite_true, zero_add,
        le_refl]
    · simp only [hA, hB, not_false_eq_true, and_self, ite_true, ite_false, add_zero,
        le_refl]
    · simpa only [hA, hB, false_and, ite_false, ite_true, zero_add] using hμ ω
    · simp only [hA, hB, false_and, ite_false, add_zero, le_refl]
  linarith

theorem eventMass_sub_sum_le_all_good {ι : Type*} [Fintype ι]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A : Ω → Prop)
    (bad : ι → Ω → Prop) :
    eventMass μ A - (∑ i, eventMass μ (bad i)) ≤
      eventMass μ (fun ω => A ω ∧ ∀ i, ¬ bad i ω) := by
  classical
  have hremove := eventMass_sub_le_and_not μ hμ A (fun ω => ∃ i, bad i ω)
  have hunion := eventMass_exists_le_sum μ hμ bad
  have hevent : (fun ω => A ω ∧ ¬ (∃ i, bad i ω)) =
      (fun ω => A ω ∧ ∀ i, ¬ bad i ω) := by
    funext ω
    simp only [not_exists]
  rw [hevent] at hremove
  linarith

theorem weightedMean_le_quarter_add_tail (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (N : ℝ) (hN : 0 ≤ N) (hX : ∀ ω, X ω ≤ N) :
    weightedMean μ X ≤ N / 4 + N * eventMass μ (fun ω => N / 4 ≤ X ω) := by
  classical
  have hpoint : ∀ ω, μ ω * X ω ≤
      (N / 4) * μ ω + N * (if N / 4 ≤ X ω then μ ω else 0) := by
    intro ω
    by_cases htail : N / 4 ≤ X ω
    · rw [ite_eq_left htail]
      have hupper := mul_le_mul_of_nonneg_left (hX ω) (hμ ω)
      have hnonneg := mul_nonneg hN (hμ ω)
      nlinarith
    · rw [ite_eq_right htail]
      have hupper := mul_le_mul_of_nonneg_left
        (le_of_lt (lt_of_not_ge htail)) (hμ ω)
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  simpa only [weightedMean, eventMass, Finset.sum_add_distrib,
    ← Finset.mul_sum, hμsum, mul_one] using hsum

theorem quarter_le_eventMass_of_half_le_weightedMean (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (N : ℝ) (hN : 0 < N) (hX : ∀ ω, X ω ≤ N)
    (hmean : N / 2 ≤ weightedMean μ X) :
    (1 : ℝ) / 4 ≤ eventMass μ (fun ω => N / 4 ≤ X ω) := by
  have hupper := weightedMean_le_quarter_add_tail μ hμ hμsum X N hN.le hX
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith

theorem quarter_sub_failure_le_tail_all_good (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (n : ℕ) (hn : 0 < n) (X : Ω → ℝ) (hX : ∀ ω, X ω ≤ (n : ℝ))
    (hmean : (n : ℝ) / 2 ≤ weightedMean μ X)
    (bad : Fin n → Ω → Prop) (ε : ℝ)
    (hbad : ∀ i, eventMass μ (bad i) ≤ ε) :
    (1 : ℝ) / 4 - (n : ℝ) * ε ≤
      eventMass μ (fun ω => (n : ℝ) / 4 ≤ X ω ∧ ∀ i, ¬ bad i ω) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have htail := quarter_le_eventMass_of_half_le_weightedMean
    μ hμ hμsum X (n : ℝ) hnR hX hmean
  have hremove := eventMass_sub_sum_le_all_good μ hμ
    (fun ω => (n : ℝ) / 4 ≤ X ω) bad
  have hsum : (∑ i, eventMass μ (bad i)) ≤ (n : ℝ) * ε := by
    calc
      (∑ i, eventMass μ (bad i)) ≤ ∑ _ : Fin n, ε :=
        Finset.sum_le_sum (fun i _ => hbad i)
      _ = (n : ℝ) * ε := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

theorem three_twentieths_le_tail_all_good (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (n : ℕ) (hn : 0 < n) (X : Ω → ℝ) (hX : ∀ ω, X ω ≤ (n : ℝ))
    (hmean : (n : ℝ) / 2 ≤ weightedMean μ X)
    (bad : Fin n → Ω → Prop)
    (hbad : ∀ i, eventMass μ (bad i) ≤ 1 / (10 * (n : ℝ))) :
    (3 : ℝ) / 20 ≤
      eventMass μ (fun ω => (n : ℝ) / 4 ≤ X ω ∧ ∀ i, ¬ bad i ω) := by
  have h := quarter_sub_failure_le_tail_all_good
    μ hμ hμsum n hn X hX hmean bad (1 / (10 * (n : ℝ))) hbad
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hconstant : (1 : ℝ) / 4 - (n : ℝ) * (1 / (10 * (n : ℝ))) = 3 / 20 := by
    field_simp [hn0] ; ring
  rw [hconstant] at h
  exact h

end MarkovSuperreflexivity.FiniteWalkDrift

end OAI
