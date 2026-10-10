import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleHistory

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

private theorem real_mean_sum {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (F : α→β→ℝ) :
    μ.mean (fun a => ∑b,F a b)=∑b,μ.mean (fun a => F a b) := by
  simp only [FinitePrior.mean,Finset.mul_sum]
  exact Finset.sum_comm

private theorem real_weighted_pair_exchange {α β γ : Type*}
    [Fintype β] [Fintype γ] (S : Finset α) (w : α→ℝ) (F : α→β→γ→ℝ) :
    (∑a∈S,w a*(∑b,∑c,F a b c))=∑b,∑c,∑a∈S,w a*F a b c := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  exact Finset.sum_comm

def diagonalSingleXiPair (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource)
    (m b s : ℕ) (X G tb td : ℝ) (l : ℕ)
    (c₁ c₂ : HistoryChoices sources seed V l) : ℝ :=
  (spectatorPrior spectator m).mean (fun ds =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mean (fun u =>
      ∑p∈integerPivotCell G,externalPivotWeight G p*
        (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mean (fun x =>
          ∑v : AllowedFrequency V l,
            diagonalSmallTerm d sources seed V giant (spectatorList spectator ds) l p u (x,v)*
              ((choicesMass sources seed V l c₁*choicesMass sources seed V l c₂)*
                (supportedHistoryPairXi d V (spectatorList spectator ds) b s X tb td G
                  (decodeHistory sources seed V l
                    (remainingState sources (Template.current seed l) (l+1) giant p u x v.val) c₁)
                  (decodeHistory sources seed V l
                    (remainingState sources (Template.current seed l) (l+1) giant p u x v.val) c₂)).re))))

theorem diagonalSingleEnergy_eq_Xi_pairs (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource)
    (m b s : ℕ) (X G tb td : ℝ) (l : ℕ) :
    diagonalSingleEnergy d sources seed V giant spectator m X G
      (Arithmetic.sourceStateBins b s tb td) l=
      ∑c₁ : HistoryChoices sources seed V l,∑c₂ : HistoryChoices sources seed V l,
        diagonalSingleXiPair d sources seed V giant spectator m b s X G tb td l c₁ c₂ := by
  unfold diagonalSingleEnergy diagonalSingleXiPair
  simp_rw [diagonalCoefficientTerm,actualCoefficient_norm_sq_eq_Xi_pairs,
    real_weighted_pair_exchange,real_mean_sum,real_weighted_pair_exchange,real_mean_sum]

end Ostmann.Construction

end

end OAI
