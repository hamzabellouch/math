import OAI.NumberTheory.Ostmann.Construction.ActualHistoryPairXi
import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate FourierTransform Classical
namespace Ostmann.Construction
open Arithmetic HistoryPairPattern

theorem decoded_same_state_rootGiantsAgree (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c₁ c₂ : HistoryChoices sources seed V l) :
    RootGiantsAgree (decodeHistory sources seed V l a c₁)
      (decodeHistory sources seed V l a c₂) := by
  constructor <;> simp only [decodeHistory_root]

theorem actualCoefficient_norm_sq_eq_Xi_pairs (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (b s : ℕ) (X tb td G : ℝ) (l : ℕ) (a : State) :
    ‖actualCoefficient sources seed V X G (residueTransform d)
      (sourceStateBins b s tb td) outside l a‖^2=
    ∑c₁ : HistoryChoices sources seed V l,∑c₂ : HistoryChoices sources seed V l,
      (choicesMass sources seed V l c₁*choicesMass sources seed V l c₂)*
        (supportedHistoryPairXi d V outside b s X tb td G
          (decodeHistory sources seed V l a c₁) (decodeHistory sources seed V l a c₂)).re := by
  have hp : actualCoefficient sources seed V X G (residueTransform d)
      (sourceStateBins b s tb td) outside l a *
      conj (actualCoefficient sources seed V X G (residueTransform d)
        (sourceStateBins b s tb td) outside l a)=
      ∑c₁ : HistoryChoices sources seed V l,∑c₂ : HistoryChoices sources seed V l,
        ((choicesMass sources seed V l c₁*choicesMass sources seed V l c₂:ℝ):ℂ)*
          supportedHistoryPairXi d V outside b s X tb td G
            (decodeHistory sources seed V l a c₁) (decodeHistory sources seed V l a c₂) := by
    simp only [actualCoefficient_eq_histories]
    rw [finite_weighted_pair_expansion]
    apply Finset.sum_congr rfl
    intro c₁ hc₁
    apply Finset.sum_congr rfl
    intro c₂ hc₂
    rw [mul_assoc]
    congr 1
    exact supportedWeight_pair_eq_Xi d V outside b s X tb td G _ _
      (decoded_same_state_rootGiantsAgree sources seed V l a c₁ c₂)
  have hr := congrArg Complex.re hp
  simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_re,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] using hr

end Ostmann.Construction

end

end OAI
