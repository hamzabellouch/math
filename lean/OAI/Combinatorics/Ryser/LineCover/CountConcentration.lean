import OAI.Combinatorics.Ryser.LineCover.Deletion
import OAI.Combinatorics.Ryser.Probability.Concentration

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem prob_rare_le_of_pointwise (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (p₀ : ℝ)
    (hpoint : ∀ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) ≤ p₀) :
    μ.prob (rare ignore test) ≤ (test.card : ℝ) * p₀ := by
  calc
    _ ≤ ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
      prob_rare_le μ ignore test
    _ ≤ ∑ _x ∈ test, p₀ := Finset.sum_le_sum fun x hx => hpoint x hx
    _ = (test.card : ℝ) * p₀ := by simp

theorem retainedCount_coordinate_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * (2 * (D : ℝ) * (H : ℝ)) ^ 2 ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.coordinate_concentration n μ (retainedCount ignore test)
    (fun _ => 2 * (D : ℝ) * (H : ℝ)) M V u hM hV hu
  · intro i ω a
    have hold : ((contribution ignore test (ω i)).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test (ω i) H hshape
    have hnew : ((contribution ignore test a).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test a H hshape
    apply (retainedCount_update_abs_le ignore test ω i a).trans
    linarith
  · intro i
    exact hCM
  · simpa using hCV

theorem retainedCount_rare_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.rare_anchor_concentration n μ (retainedCount ignore test)
    (emptyOutcome shapes D) (fun _ => (D : ℝ) * (H : ℝ))
    (fun _ => (test.card : ℝ) * p₀) (fun _ => rare ignore test)
    M V u hM hV hu
  · intro i ω
    exact retainedCount_empty_abs_le_mul ignore test H hshape ω i
  · intro i ω h
    exact not_rare_retainedCount_eq ignore test ω i h
  · intro i
    exact prob_rare_le_of_pointwise (μ i) ignore test p₀ (hpoint i)
  · intro i
    simpa only [mul_assoc] using hCM
  · simpa [mul_assoc] using hCV

theorem prob_lt_le_prob_centered {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ)
    (hmean : 2 * u ≤ ν.expectation f) :
    ν.prob (fun ω => f ω < u) ≤
      ν.prob (fun ω => u ≤ |f ω - ν.expectation f|) := by
  apply ν.prob_mono
  intro ω hω
  have hneg := neg_le_abs (f ω - ν.expectation f)
  linarith

theorem retainedCount_coordinate_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * (2 * (D : ℝ) * (H : ℝ)) ^ 2 ≤ V)
    (hmean : 2 * u ≤ (FiniteLaw.pi μ).expectation (retainedCount ignore test)) :
    (FiniteLaw.pi μ).prob (fun ω => retainedCount ignore test ω < u) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
  (prob_lt_le_prob_centered (FiniteLaw.pi μ) (retainedCount ignore test) u hmean).trans
    (retainedCount_coordinate_concentration μ ignore test H hshape M V u
      hM hV hu hCM hCV)

theorem retainedCount_rare_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V)
    (hmean : 2 * u ≤ (FiniteLaw.pi μ).expectation (retainedCount ignore test)) :
    (FiniteLaw.pi μ).prob (fun ω => retainedCount ignore test ω < u) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
  (prob_lt_le_prob_centered (FiniteLaw.pi μ) (retainedCount ignore test) u hmean).trans
    (retainedCount_rare_concentration μ ignore test H hshape p₀ hpoint M V u
      hM hV hu hCM hCV)

theorem expectation_retainedCount_ge_of_base_survival
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (δ : ℝ)
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    δ * (test.card : ℝ) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
  rw [expectation_retainedCount]
  calc
    δ * (test.card : ℝ) = ∑ _x ∈ test, δ := by simp [mul_comm]
    _ ≤ ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (hbase x hx).trans
      apply (FiniteLaw.pi μ).prob_mono
      intro ω hω
      exact survivors_mono_ignore (Finset.empty_subset ignore) ω hω

end RyserCoveringCounterexample.LineCover

end

end OAI
