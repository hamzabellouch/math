import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordMain

namespace OAI

/-! # Worst-case Subset Sum in one-fifth-exponential space

The threshold is chosen once from its proved existence theorem. No solution,
deficiency statistic, or bit-length exponent is an input. The finite random-word
experiment has one-sided correctness, success probability at least two thirds,
and bounds on its operation and writable-storage counts on every outcome.
-/

noncomputable section
namespace LowSpaceSubsetSum

def algorithm {n : ℕ} (I : Instance n) (words : WordFinalDecision.Words I) :
    (Bool × ℕ) × ℕ := WordFinalDecision.run decisionThreshold I words

/-- One-sided randomized correctness and all-outcome resource-count bounds. -/
theorem worst_case_subset_sum :
    (∀ (n : ℕ) (I : Instance n) (words : WordFinalDecision.Words I),
      (algorithm I words).1.1 = true → Solvable I) ∧
    (∀ (n : ℕ) (I : Instance n), Solvable I →
      (2/3 : ℝ) ≤ (FiniteLaw.uniform : FiniteLaw (WordFinalDecision.Words I)).probability
        (fun words => (algorithm I words).1.1 = true)) ∧
    (∀ c : ℕ, 0 < c → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ I : Instance n, inputBits I ≤ n^c → ∀ words : WordFinalDecision.Words I,
        ((algorithm I words).1.2 : ℝ) ≤
          (4*(3 : ℝ)^624)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) ∧
        ((algorithm I words).2 : ℝ) ≤
          2*(inputScale I : ℝ)^15*(2 : ℝ)^((199/1000 : ℝ)*n)) :=
  ⟨fun _ I words => WordFinalDecision.sound decisionThreshold I words,
    fun _ I => WordFinalDecision.probability decisionThreshold I,
    WordMain.main_resources decisionThreshold⟩

/-- The writable-storage count has every fixed exponential rate above .199. -/
theorem exponential_space (rho : ℝ) (hrho : (199/1000 : ℝ) < rho) (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ I : Instance n, inputBits I ≤ n^c →
      ∀ words : WordFinalDecision.Words I,
        ((algorithm I words).1.2 : ℝ) ≤
          (4*(3 : ℝ)^624)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) ∧
        ((algorithm I words).2 : ℝ) ≤ (2*(3 : ℝ)^15)*(2 : ℝ)^(rho*n) :=
  WordMain.space_corollary decisionThreshold rho hrho c hc

/-- In particular, ordinary one-fifth-exponential writable space. -/
theorem one_fifth_space (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ I : Instance n, inputBits I ≤ n^c →
      ∀ words : WordFinalDecision.Words I,
        ((algorithm I words).1.2 : ℝ) ≤
          (4*(3 : ℝ)^624)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) ∧
        ((algorithm I words).2 : ℝ) ≤ (2*(3 : ℝ)^15)*(2 : ℝ)^((1/5 : ℝ)*n) :=
  exponential_space (1/5) (by norm_num) c hc

theorem algorithm_word_width {n : ℕ} (I : Instance n) :
    wordWidth I = 4*(n+inputBits I+2) := rfl

end LowSpaceSubsetSum

end

end OAI
