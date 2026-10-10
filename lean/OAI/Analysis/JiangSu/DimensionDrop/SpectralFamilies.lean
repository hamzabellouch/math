import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
namespace JiangSuConstruction

variable {p q : ℕ}
abbrev SpectralIndex (m : Multiplicities p q) := Fin m.lower ⊕ (Fin m.upper ⊕ Fin m.residual)
def spectralFamily (m : Multiplicities p q) : SpectralIndex m → C(Interval,Interval)
  | .inl _ => lowerEigenvalue
  | .inr (.inl _) => upperEigenvalue
  | .inr (.inr _) => ContinuousMap.id _

def sumShuffle (α β γ : Type*) : (α⊕(β⊕γ)) ≃ ((α⊕γ)⊕β) where
  toFun | .inl a => .inl (.inl a) | .inr (.inl b) => .inr b | .inr (.inr c) => .inl (.inr c)
  invFun | .inl (.inl a) => .inl a | .inl (.inr c) => .inr (.inr c) | .inr b => .inr (.inl b)
  left_inv := by rintro (a|b|c) <;> rfl
  right_inv := by rintro ((a|c)|b) <;> rfl

def sumShuffleRight (α β γ : Type*) : (α⊕(β⊕γ)) ≃ ((β⊕γ)⊕α) :=
  Equiv.sumComm α (β⊕γ)

def zeroCountEquiv (m : Multiplicities p q) : (Fin m.lower ⊕ Fin m.residual) ≃
    (Fin (m.k-q*m.delta)×Fin m.l) := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.zero_count)
def upperCountEquiv (m : Multiplicities p q) : Fin m.upper ≃
    (Fin m.delta×(Fin q×Fin m.l)) := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.upper_eq)
def oneCountEquiv (m : Multiplicities p q) : (Fin m.upper ⊕ Fin m.residual) ≃
    (Fin (m.l-p*m.gamma)×Fin m.k) := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.one_count)
def lowerCountEquiv (m : Multiplicities p q) : Fin m.lower ≃
    (Fin m.gamma×(Fin p×Fin m.k)) := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.lower_eq)

def zeroBlockEquiv (m : Multiplicities p q) : SpectralIndex m ≃
    ((Fin (m.k-q*m.delta)×Fin m.l) ⊕ (Fin m.delta×(Fin q×Fin m.l))) :=
  (sumShuffle _ _ _).trans (Equiv.sumCongr (zeroCountEquiv m) (upperCountEquiv m))

def oneBlockEquiv (m : Multiplicities p q) : SpectralIndex m ≃
    ((Fin (m.l-p*m.gamma)×Fin m.k) ⊕ (Fin m.gamma×(Fin p×Fin m.k))) :=
  (sumShuffleRight _ _ _).trans (Equiv.sumCongr (oneCountEquiv m) (lowerCountEquiv m))

lemma spectralFamily_zero (m : Multiplicities p q) (z) :
    spectralFamily m ((zeroBlockEquiv m).symm z) leftEndpoint =
      (match z with | Sum.inl _ => leftEndpoint | Sum.inr _ => midpoint) := by
  cases z with
  | inl z =>
    change spectralFamily m
      ((sumShuffle _ _ _).symm (Sum.inl ((zeroCountEquiv m).symm z))) leftEndpoint =
        leftEndpoint
    cases (zeroCountEquiv m).symm z <;> apply Subtype.ext <;>
      norm_num [sumShuffle,spectralFamily,lowerEigenvalue,leftEndpoint]
  | inr z =>
    apply Subtype.ext
    norm_num [zeroBlockEquiv, sumShuffle, spectralFamily, upperEigenvalue, leftEndpoint,
      midpoint]
lemma spectralFamily_one (m : Multiplicities p q) (z) :
    spectralFamily m ((oneBlockEquiv m).symm z) rightEndpoint =
      (match z with | Sum.inl _ => rightEndpoint | Sum.inr _ => midpoint) := by
  cases z with
  | inl z =>
    change spectralFamily m
      ((sumShuffleRight _ _ _).symm (Sum.inl ((oneCountEquiv m).symm z))) rightEndpoint =
        rightEndpoint
    cases (oneCountEquiv m).symm z <;> apply Subtype.ext <;>
      norm_num [sumShuffleRight,spectralFamily,upperEigenvalue,rightEndpoint]
  | inr z =>
    apply Subtype.ext
    norm_num [oneBlockEquiv, sumShuffleRight, spectralFamily, lowerEigenvalue, rightEndpoint,
      midpoint]

lemma spectralFamily_surjective (m : Multiplicities p q) :
    ∃ z, Function.Surjective (spectralFamily m z) :=
  ⟨Sum.inr (Sum.inr ⟨0,m.residual_pos⟩),Function.surjective_id⟩

end JiangSuConstruction






namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


lemma diagonalContinuousHom_injective (ξ : κ → C(Interval,Interval)) (k : κ)
    (hk : Function.Surjective (ξ k)) : Function.Injective (diagonalContinuousHom (ι := ι) ξ) := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  obtain ⟨s,rfl⟩ := hk t
  have evaluatedEquality :=
    congrArg (fun matrix : C(Interval, CStarMatrix (ι × κ) (ι × κ) ℂ) => matrix s) h
  exact congrFun (blockDiagonalHom_injective evaluatedEquality) k

end JiangSuConstruction

end

end OAI
