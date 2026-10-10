import OAI.NumberTheory.Ostmann.Construction.DiagonalEnvironment
import OAI.NumberTheory.Ostmann.Construction.DiagonalHistoryExpansion

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

private theorem weighted_sum_pair_exchange {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset ℕ) (w : ℕ→ℂ) (F : ℕ→α→β→ℂ) :
    (∑p∈S,w p*(∑a,∑b,F p a b))=∑a,∑b,∑p∈S,w p*F p a b := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact Finset.sum_comm

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (seed : List SourceSlot)
    (V : ℕ→ℕ) (spectator : PrimeSource) (m : ℕ) (X : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) (B Δ : ℝ)
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)

def diagonalHistoryCovariance (c₁ c₂ : HistoryChoices C.sources seed V l)
    (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  (spectatorPrior spectator m).cmean (fun ds =>
    (assignmentPrior C.sources U).cmean (fun u =>
      ∑p∈integerPivotCell C.giantCenter,(externalPivotWeight C.giantCenter p:ℂ)*
        C.correctedHistoryPairExpression seed V X bins (spectatorList spectator ds) l B Δ p u c₁ c₂ e))

theorem diagonalCovariance_eq_history_pairs (e : Equiv.Perm (RemainingIndex T)) :
    C.diagonalCovariance seed V spectator m X bins l B Δ e=
      ∑c₁ : HistoryChoices C.sources seed V l,∑c₂ : HistoryChoices C.sources seed V l,
        C.diagonalHistoryCovariance seed V spectator m X bins l B Δ c₁ c₂ e := by
  unfold diagonalCovariance diagonalHistoryCovariance
  simp_rw [C.correctedSmallCounterpartExpression_eq_history_pairs,
    weighted_sum_pair_exchange,FinitePrior.cmean_sum]

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
