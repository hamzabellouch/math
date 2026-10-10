import Mathlib

namespace OAI

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace YauCounterexamples
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
def complexGramTrace (b : Basis ι ℝ E) (H : E → E → ℂ) : ℂ :=
  ∑ i, ∑ j, ((Matrix.gram ℝ b)⁻¹ i j : ℂ)*H (b i) (b j)
lemma complexGramTrace_add (b : Basis ι ℝ E) (H K : E → E → ℂ) :
    complexGramTrace b (fun v w => H v w+K v w) =
      complexGramTrace b H+complexGramTrace b K := by
  simp [complexGramTrace,mul_add,Finset.sum_add_distrib]
lemma complexGramTrace_sub (b : Basis ι ℝ E) (H K : E → E → ℂ) :
    complexGramTrace b (fun v w => H v w-K v w) =
      complexGramTrace b H-complexGramTrace b K := by
  simp [complexGramTrace,mul_sub,Finset.sum_sub_distrib]
lemma complexGramTrace_mul_left (b : Basis ι ℝ E) (c : ℂ) (H : E → E → ℂ) :
    complexGramTrace b (fun v w => c*H v w) = c*complexGramTrace b H := by
  unfold complexGramTrace
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma complexGramTrace_mul_right (b : Basis ι ℝ E) (c : ℂ) (H : E → E → ℂ) :
    complexGramTrace b (fun v w => H v w*c) = complexGramTrace b H*c := by
  simpa only [mul_comm] using complexGramTrace_mul_left b c H
lemma complexGramTrace_flip (b : Basis ι ℝ E) (H : E → E → ℂ) :
    complexGramTrace b (fun v w => H w v) = complexGramTrace b H := by
  unfold complexGramTrace
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs := ((Matrix.isHermitian_gram ℝ b).inv).apply i j
  simp only [star_trivial] at hs
  rw [hs]
end YauCounterexamples
end

end OAI
