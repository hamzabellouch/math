import OAI.NumberTheory.Ostmann.Construction.ActualHistoryPairXi
import OAI.NumberTheory.Ostmann.Construction.DiagonalHistoryExpansion

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (seed : List SourceSlot)
    (V : ℕ→ℕ) (b s : ℕ) (X tb td : ℝ) (outside : List ℕ) (l : ℕ) (B Δ : ℝ)
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)

def diagonalPairXiTerm (p : ℕ) (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant) (v : AllowedFrequency V l)
    (c₁ c₂ : HistoryChoices C.sources seed V l) (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  if he : CounterpartCompatible C.sources T C.giant x e then
    if PreservesRemainingBands T e then
      let y := reconstructCounterpart C.sources T C.giant x e he
      let h := decodeHistory C.sources seed V l
        (remainingState C.sources (Template.current seed l) (l+1) C.giant p u x v.val) c₁
      let j := decodeHistory C.sources seed V l
        (remainingState C.sources (Template.current seed l) (l+1) C.giant p u y v.val) c₂
      (remainingCounterpart C.sources (Template.current seed l) (l+1) C.giant
        (C.giantCenter+B+Δ) B C.giantCenter (C.cells.center (Conclusion.bulkSize k L/2)) u y:ℂ)*
        supportedHistoryPairXi d V outside b s X tb td C.giantCenter h j
    else 0
  else 0

theorem diagonalHistory_pair_eq_Xi (p : ℕ) (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant) (v : AllowedFrequency V l)
    (c₁ c₂ : HistoryChoices C.sources seed V l) (e : Equiv.Perm (RemainingIndex T)) :
    C.diagonalHistoryWeight seed V X (Arithmetic.sourceStateBins b s tb td) outside l p u x v c₁*
      conj (C.correctedCounterpartTerm seed l B Δ u x
        (fun y => C.diagonalHistoryWeight seed V X (Arithmetic.sourceStateBins b s tb td) outside l p u y v c₂) e)=
    C.diagonalPairXiTerm seed V b s X tb td outside l B Δ p u x v c₁ c₂ e := by
  unfold correctedCounterpartTerm diagonalPairXiTerm
  split_ifs with hc hb
  · simp only [map_mul,Complex.conj_ofReal]
    rw [show ∀a z w : ℂ,a*(z*w)=z*(a*w) from fun a z w => by ring]
    congr 1
    exact supportedWeight_pair_eq_Xi d V outside b s X tb td C.giantCenter _ _
      (decoded_counterpart_rootGiantsAgree C.sources seed V C.giant l p u x v.val e hc hb c₁ c₂)
  · simp only [map_zero,mul_zero]
  · simp only [map_zero,mul_zero]

theorem correctedHistoryPairExpression_eq_Xi (p : ℕ) (u : SourceAssignment C.sources U)
    (c₁ c₂ : HistoryChoices C.sources seed V l) (e : Equiv.Perm (RemainingIndex T)) :
    C.correctedHistoryPairExpression seed V X (Arithmetic.sourceStateBins b s tb td) outside l B Δ p u c₁ c₂ e=
    ∑x : RemainingSample C.sources T C.giant,∑v : AllowedFrequency V l,
      ((remainingPrior C.sources T C.giant).mass x:ℂ)*
      (diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v):ℂ)*
      ((choicesMass C.sources seed V l c₁*choicesMass C.sources seed V l c₂:ℝ):ℂ)*
      C.diagonalPairXiTerm seed V b s X tb td outside l B Δ p u x v c₁ c₂ e := by
  unfold correctedHistoryPairExpression
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  rw [←C.diagonalHistory_pair_eq_Xi seed V b s X tb td outside l B Δ p u x v c₁ c₂ e]
  ring

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
