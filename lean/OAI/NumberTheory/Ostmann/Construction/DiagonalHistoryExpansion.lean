import OAI.NumberTheory.Ostmann.Construction.ActualHistoryPairExpansion

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

private theorem four_sum_rotate {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (F : α→β→γ→δ→ℂ) :
    (∑a,∑b,∑c,∑d,F a b c d)=∑c,∑d,∑a,∑b,F a b c d := by
  calc
    _ = ∑a,∑c,∑b,∑d,F a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑c,∑a,∑b,∑d,F a b c d := Finset.sum_comm
    _ = ∑c,∑a,∑d,∑b,F a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (seed : List SourceSlot)
    (V : ℕ→ℕ) (X : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ)
    (l : ℕ) (B Δ : ℝ)
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)

def diagonalHistoryWeight (p : ℕ) (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant) (v : AllowedFrequency V l)
    (c : HistoryChoices C.sources seed V l) : ℂ :=
  actualHistoryWeight C.sources seed V X C.giantCenter (residueTransform d) bins outside l
    (remainingState C.sources (Template.current seed l) (l+1) C.giant p u x v.val) c

theorem diagonalCoefficient_pair_eq_history_pairs
    (p : ℕ) (u : SourceAssignment C.sources U) (x : RemainingSample C.sources T C.giant)
    (v : AllowedFrequency V l) (e : Equiv.Perm (RemainingIndex T)) :
    diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v)*
      conj (C.correctedCounterpartTerm seed l B Δ u x
        (fun y => diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (y,v)) e)=
    ∑c₁ : HistoryChoices C.sources seed V l,∑c₂ : HistoryChoices C.sources seed V l,
      ((choicesMass C.sources seed V l c₁*choicesMass C.sources seed V l c₂:ℝ):ℂ)*
        C.diagonalHistoryWeight seed V X bins outside l p u x v c₁*
        conj (C.correctedCounterpartTerm seed l B Δ u x
          (fun y => C.diagonalHistoryWeight seed V X bins outside l p u y v c₂) e) := by
  unfold diagonalCoefficientTerm
  simp_rw [actualCoefficient_eq_histories,C.correctedCounterpartTerm_sum,C.correctedCounterpartTerm_cmul]
  exact finite_weighted_pair_expansion _ _ _ _

def correctedHistoryPairExpression (p : ℕ) (u : SourceAssignment C.sources U)
    (c₁ c₂ : HistoryChoices C.sources seed V l) (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  ∑x : RemainingSample C.sources T C.giant,∑v : AllowedFrequency V l,
    ((remainingPrior C.sources T C.giant).mass x:ℂ)*
      (diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v):ℂ)*
      ((choicesMass C.sources seed V l c₁*choicesMass C.sources seed V l c₂:ℝ):ℂ)*
      C.diagonalHistoryWeight seed V X bins outside l p u x v c₁*
      conj (C.correctedCounterpartTerm seed l B Δ u x
        (fun y => C.diagonalHistoryWeight seed V X bins outside l p u y v c₂) e)

theorem correctedSmallCounterpartExpression_eq_history_pairs
    (p : ℕ) (u : SourceAssignment C.sources U) (e : Equiv.Perm (RemainingIndex T)) :
    C.correctedSmallCounterpartExpression seed V X bins outside l B Δ p u e=
      ∑c₁ : HistoryChoices C.sources seed V l,∑c₂ : HistoryChoices C.sources seed V l,
        C.correctedHistoryPairExpression seed V X bins outside l B Δ p u c₁ c₂ e := by
  unfold correctedSmallCounterpartExpression correctedHistoryPairExpression
  calc
    _ = ∑x : RemainingSample C.sources T C.giant,∑v : AllowedFrequency V l,
        ((remainingPrior C.sources T C.giant).mass x:ℂ)*
        (diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v):ℂ)*
        (diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v)*
          conj (C.correctedCounterpartTerm seed l B Δ u x
            (fun y => diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (y,v)) e)) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      simp_rw [C.diagonalCoefficient_pair_eq_history_pairs seed V X bins outside l B Δ,
        Finset.mul_sum]
      rw [four_sum_rotate]
      apply Finset.sum_congr rfl
      intro c₁ hc₁
      apply Finset.sum_congr rfl
      intro c₂ hc₂
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro v hv
      ring

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
