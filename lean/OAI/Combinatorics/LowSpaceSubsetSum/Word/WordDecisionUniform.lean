import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordDecisionRound

namespace OAI

/-! # The round and repetition laws are uniform on finite fair-word tables -/

noncomputable section
namespace LowSpaceSubsetSum.WordDecisionUniform

open scoped BigOperators

private theorem law_ext {A : Type} [Fintype A] (μ ν : FiniteLaw A)
    (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem uniform_prod {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (FiniteLaw.uniform : FiniteLaw A).prod (FiniteLaw.uniform : FiniteLaw B) =
      (FiniteLaw.uniform : FiniteLaw (A × B)) := by
  apply law_ext
  funext x
  simp only [FiniteLaw.prod,FiniteLaw.uniform,Fintype.card_prod,Nat.cast_mul]
  exact one_div_mul_one_div _ _

theorem uniform_iid {A : Type} [Fintype A] [Nonempty A] (k : ℕ) :
    (FiniteLaw.uniform : FiniteLaw A).iid k =
      (FiniteLaw.uniform : FiniteLaw (Fin k → A)) := by
  apply law_ext
  funext x
  simp only [FiniteLaw.iid,FiniteLaw.pi,FiniteLaw.uniform,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Fintype.card_fun,Nat.cast_pow,one_div_pow]

theorem round_law {n : ℕ} (I : Instance n) :
    WordDecisionRound.law I = (FiniteLaw.uniform : FiniteLaw (WordDecisionRound.Words I)) :=
  uniform_prod

theorem repeated_probability {n : ℕ} (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (hden : ((mixerSize n/2 : ℕ) : ℝ)+1 <
      (2 : ℝ)^((1/1500 : ℝ)*(mixerSize n/2 : ℕ))) (hs : Solvable I) :
    (2/3 : ℝ) <
      (FiniteLaw.uniform : FiniteLaw (Fin (inputScale I^120) → WordDecisionRound.Words I)).probability
        (fun words => (WordDecisionRound.repeated I hn hscale words).1.1 = true) := by
  have h := WordDecisionRound.repeated_probability I hn hscale hden hs
  rw [round_law,uniform_iid] at h
  exact h

end LowSpaceSubsetSum.WordDecisionUniform

end

end OAI
