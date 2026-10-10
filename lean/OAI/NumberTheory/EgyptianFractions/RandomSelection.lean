import OAI.NumberTheory.EgyptianFractions.SimultaneousSelection
import OAI.NumberTheory.EgyptianFractions.IndependentBlockSelection

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomSelection

/-- A simultaneous variable-threshold Markov bound on the fraction of bad samples. -/
theorem bad_threshold_fraction_le {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (tests : Finset J) (score : Ω → J → ℝ)
    (threshold ε : J → ℝ)
    (hnonneg : ∀ ω, ∀ j ∈ tests, 0 ≤ score ω j)
    (hpos : ∀ j ∈ tests, 0 < threshold j)
    (hmean : ∀ j ∈ tests, (∑ ω, score ω j) ≤
      (Fintype.card Ω : ℝ) * ε j * threshold j) :
    ((Finset.univ.filter (fun ω => ∃ j ∈ tests, threshold j < score ω j)).card : ℝ) /
      Fintype.card Ω ≤ ∑ j ∈ tests, ε j := by
  classical
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hfilter :
      Finset.univ.filter (fun ω => ∃ j ∈ tests, threshold j < score ω j) =
      Finset.univ.filter (fun ω => ∃ j ∈ tests, 1 < score ω j / threshold j) := by
    apply Finset.filter_congr
    intro ω _
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [lt_div_iff₀ (hpos j hj), one_mul]
  rw [hfilter]
  apply (div_le_iff₀ hΩ).2
  have hmarkov := card_exists_large_score_mul_le Finset.univ tests
    (fun ω j => score ω j / threshold j) 1
    (fun ω _ j hj => div_nonneg (hnonneg ω j hj) (hpos j hj).le)
  simp only [mul_one] at hmarkov
  calc
    ((Finset.univ.filter (fun ω => ∃ j ∈ tests, 1 < score ω j / threshold j)).card : ℝ) ≤
        ∑ j ∈ tests, ∑ ω, score ω j / threshold j := hmarkov
    _ = ∑ j ∈ tests, (∑ ω, score ω j) / threshold j := by
      simp_rw [Finset.sum_div]
    _ ≤ ∑ j ∈ tests, (Fintype.card Ω : ℝ) * ε j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (div_le_iff₀ (hpos j hj)).2 (hmean j hj)
    _ = (∑ j ∈ tests, ε j) * Fintype.card Ω := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A finite realization simultaneously meeting all middle-level mean thresholds
    and enjoying a successful block for every terminal integer. -/
theorem exists_middle_thresholds_and_terminal_blocks (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω J : Type) [Fintype Ω] [Nonempty Ω]
      (tests : Finset J) (score : Ω → J → ℝ) (threshold ε : J → ℝ)
      (s : Finset ℕ) (B : ℕ → Finset Ω),
      (∀ ω, ∀ j ∈ tests, 0 ≤ score ω j) →
      (∀ j ∈ tests, 0 < threshold j) →
      (∀ j ∈ tests, (∑ ω, score ω j) ≤
        (Fintype.card Ω : ℝ) * ε j * threshold j) →
      (∑ j ∈ tests, ε j) ≤ δ →
      (∀ u ∈ s, N ≤ u) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤
        (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω, (∀ j ∈ tests, score (f 0) j ≤ threshold j) ∧
        ∀ u ∈ s, ∃ i : Fin 1000, f i ∉ B u := by
  classical
  obtain ⟨N, hN⟩ := IndependentBlockSelection.exists_middle_and_terminal_blocks δ hδ
  refine ⟨N, ?_⟩
  intro Ω J _ _ tests score threshold ε s B hnonneg hpos hmean hε hs hbad
  let middleBad := Finset.univ.filter (fun ω => ∃ j ∈ tests, threshold j < score ω j)
  have hmiddle : (middleBad.card : ℝ) / Fintype.card Ω ≤ δ :=
    (bad_threshold_fraction_le tests score threshold ε hnonneg hpos hmean).trans hε
  obtain ⟨f, hf, hterminal⟩ := hN Ω s B middleBad hs hmiddle hbad
  refine ⟨f, ?_, hterminal⟩
  intro j hj
  by_contra h
  apply hf
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, lt_of_not_ge h⟩

end Problem337.RandomSelection

end

end OAI
