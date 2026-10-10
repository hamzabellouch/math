import OAI.NumberTheory.EgyptianFractions.RandomSelection
import OAI.NumberTheory.EgyptianFractions.FourierFailureBounds

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.LevelFailureMean

/-- Fubini for counts of failing integers at a level. -/
theorem sum_failure_counts {Ω U : Type*} [Fintype Ω] [DecidableEq Ω]
    (level : Finset U) (bad : Ω → U → Prop) [DecidableRel bad] :
    (∑ ω, ((level.filter (bad ω)).card : ℝ)) =
      ∑ u ∈ level, ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

/-- Pointwise failure probabilities bound the expected number of failing
    integers on a level, without any independence between integers. -/
theorem level_failure_mean_le {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (level : Finset U) (bad : Ω → U → Prop) [DecidableRel bad]
    (X e : ℝ) (he : 0 ≤ e) (hlevel : (level.card : ℝ) ≤ X)
    (hbad : ∀ u ∈ level,
      ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ) / Fintype.card Ω ≤ e) :
    (∑ ω, ((level.filter (bad ω)).card : ℝ)) ≤
      (Fintype.card Ω : ℝ) * e * X := by
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [sum_failure_counts]
  calc
    (∑ u ∈ level, ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ)) ≤
        ∑ _u ∈ level, e * (Fintype.card Ω : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact (div_le_iff₀ hΩ).mp (hbad u hu)
    _ = (level.card : ℝ) * (e * Fintype.card Ω) := by simp
    _ ≤ X * (e * Fintype.card Ω) :=
      mul_le_mul_of_nonneg_right hlevel (by positivity)
    _ = (Fintype.card Ω : ℝ) * e * X := by ring

/-- The two middle-level exponential budgets differ by exactly `exp(-m/250)`. -/
theorem middle_level_failure_mean_le {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (level : Finset U) (bad : Ω → U → Prop) [DecidableRel bad]
    (X m : ℝ) (hlevel : (level.card : ℝ) ≤ X)
    (hbad : ∀ u ∈ level,
      ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ) / Fintype.card Ω ≤
        Real.exp (-m / 200)) :
    (∑ ω, ((level.filter (bad ω)).card : ℝ)) ≤ (Fintype.card Ω : ℝ) *
      Real.exp (-m / 250) * (X * Real.exp (-m / 1000)) := by
  have h := level_failure_mean_le level bad X (Real.exp (-m / 200))
    (Real.exp_pos _).le hlevel hbad
  have he : Real.exp (-m / 200) = Real.exp (-m / 250) * Real.exp (-m / 1000) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  convert h using 1
  ring

/-- A deliberately coarse explicit onset suffices to absorb the number of levels. -/
theorem middle_level_budget_le_half (m : ℝ) (hm : 500000 ≤ m) :
    m * Real.exp (-m / 250) ≤ 1 / 2 := by
  have hm0 : 0 ≤ m := by linarith
  have hlin := Real.add_one_le_exp (m / 500)
  have hsq : (m / 500 + 1) ^ 2 ≤ Real.exp (m / 500) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (Real.exp_pos _).le).mpr hlin
  have heq : Real.exp (m / 500) ^ 2 = Real.exp (m / 250) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsq
  have hlarge : 2 * m ≤ Real.exp (m / 250) := by
    nlinarith
  rw [show -m / 250 = -(m / 250) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  linarith

/-- Concrete finite form of the simultaneous-selection step: one block has
    few failures at every middle level, while the collection of 1000 blocks
    succeeds at every sufficiently large terminal integer. -/
theorem exists_good_levels_and_terminal_blocks :
    ∃ N : ℕ, ∀ (Ω J : Type) [Fintype Ω] [Nonempty Ω]
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ) (m : ℝ)
      (middleBad terminalBad : Ω → ℕ → Prop)
      [DecidableRel middleBad] [DecidableRel terminalBad] (terminal : Finset ℕ),
      500000 ≤ m → (tests.card : ℝ) ≤ m →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (∀ j ∈ tests, ∀ u ∈ level j,
        ((Finset.univ.filter (fun ω => middleBad ω u)).card : ℝ) /
          Fintype.card Ω ≤ Real.exp (-m / 200)) →
      (∀ u ∈ terminal, N ≤ u) →
      (∀ u ∈ terminal,
        ((Finset.univ.filter (fun ω => terminalBad ω u)).card : ℝ) /
          Fintype.card Ω ≤ (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω,
        (∀ j ∈ tests,
          (((level j).filter (middleBad (f 0))).card : ℝ) ≤
            X j * Real.exp (-m / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ¬ terminalBad (f i) u := by
  classical
  obtain ⟨N, hN⟩ := RandomSelection.exists_middle_thresholds_and_terminal_blocks
    (1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, ?_⟩
  intro Ω J _ _ tests level X m middleBad terminalBad _ _ terminal
    hm htests hX hlevel hmiddle hterminal hbad
  let score : Ω → J → ℝ := fun ω j => ((level j).filter (middleBad ω)).card
  let threshold : J → ℝ := fun j => X j * Real.exp (-m / 1000)
  let ε : J → ℝ := fun _ => Real.exp (-m / 250)
  let B : ℕ → Finset Ω := fun u => Finset.univ.filter (fun ω => terminalBad ω u)
  have hnonneg : ∀ ω, ∀ j ∈ tests, 0 ≤ score ω j := by
    intros
    exact Nat.cast_nonneg _
  have hpos : ∀ j ∈ tests, 0 < threshold j := by
    intro j hj
    exact mul_pos (hX j hj) (Real.exp_pos _)
  have hmean : ∀ j ∈ tests, (∑ ω, score ω j) ≤
      (Fintype.card Ω : ℝ) * ε j * threshold j := by
    intro j hj
    exact middle_level_failure_mean_le (level j) middleBad (X j) m
      (hlevel j hj) (hmiddle j hj)
  have herror : (∑ j ∈ tests, ε j) ≤ (1 / 2 : ℝ) := by
    dsimp [ε]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right htests (Real.exp_pos _).le).trans
      (middle_level_budget_le_half m hm)
  obtain ⟨f, hf, ht⟩ := hN Ω J tests score threshold ε terminal B
    hnonneg hpos hmean herror hterminal hbad
  refine ⟨f, hf, ?_⟩
  intro u hu
  obtain ⟨i, hi⟩ := ht u hu
  exact ⟨i, by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩

end Problem337.LevelFailureMean

end

end OAI
