import OAI.NumberTheory.Ostmann.Conclusion.SelectedCovarianceComplex
import OAI.NumberTheory.Ostmann.Construction.ActualHistoryPairXi

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction
open Conclusion Arithmetic.HistoryPairPattern
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
local notation "seed" => Template.initial (2*(bulkSize k L/2)) k
local notation "V" => frequencyBound Bs BD Bz k L

def selectedPermutedState (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (x : OuterSample C.sources (Template.current seed l) C.giant) (v : ℤ) : State :=
  outerState C.sources (Template.current seed l) C.giant
    (x.1,x.2.1,sourceAssignmentPermutation C.sources (Template.current seed l)
      (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ) x.2.2) v

def selectedPermutedHistory (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (x : OuterSample C.sources (Template.current seed l) C.giant)
    (v : AllowedFrequency V l) (c : HistoryChoices C.sources seed V l) : History l :=
  decodeHistory C.sources seed V l (C.selectedPermutedState l σ x v.val) c

theorem selectedPermutedHistory_rootGiantsAgree (l : ℕ)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (x : OuterSample C.sources (Template.current seed l) C.giant)
    (v : AllowedFrequency V l) (c₁ c₂ : HistoryChoices C.sources seed V l) :
    RootGiantsAgree (C.selectedPermutedHistory l σ x v c₁)
      (C.selectedPermutedHistory l τ x v c₂) := by
  unfold RootGiantsAgree selectedPermutedHistory
  simp only [decodeHistory_root,selectedPermutedState,outerState]
  constructor <;> trivial

def selectedCovarianceXiTerm (spectator : PrimeSource) (s l : ℕ)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*s)→spectator.Sample)
    (x : OuterSample C.sources (Template.current seed l) C.giant)
    (v : AllowedFrequency V l) (c₁ c₂ : HistoryChoices C.sources seed V l) : ℂ :=
  supportedHistoryPairXi d V (spectatorList spectator ds) (bulkSize k L/2) s
    C.scale C.bulkBin C.spectatorBin C.giantCenter
    (C.selectedPermutedHistory l σ x v c₁) (C.selectedPermutedHistory l τ x v c₂)

theorem selectedCoefficient_pair_eq_historyXi (spectator : PrimeSource) (s l : ℕ)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*s)→spectator.Sample)
    (x : OuterSample C.sources (Template.current seed l) C.giant)
    (v : AllowedFrequency V l) :
    actualCoefficient C.sources seed V C.scale C.giantCenter (residueTransform d)
      (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin)
      (spectatorList spectator ds) l (C.selectedPermutedState l σ x v.val) *
    conj (actualCoefficient C.sources seed V C.scale C.giantCenter (residueTransform d)
      (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin)
      (spectatorList spectator ds) l (C.selectedPermutedState l τ x v.val)) =
    ∑ c₁ : HistoryChoices C.sources seed V l,∑ c₂ : HistoryChoices C.sources seed V l,
      ((choicesMass C.sources seed V l c₁*choicesMass C.sources seed V l c₂:ℝ):ℂ)*
        C.selectedCovarianceXiTerm spectator s l σ τ ds x v c₁ c₂ := by
  simp_rw [actualCoefficient_eq_histories]
  rw [finite_weighted_pair_expansion]
  apply Finset.sum_congr rfl
  intro c₁ hc₁
  apply Finset.sum_congr rfl
  intro c₂ hc₂
  rw [mul_assoc]
  congr 1
  exact supportedWeight_pair_eq_Xi d V (spectatorList spectator ds) (bulkSize k L/2) s
    C.scale C.bulkBin C.spectatorBin C.giantCenter _ _
    (C.selectedPermutedHistory_rootGiantsAgree l σ τ x v c₁ c₂)

theorem selectedComplexCovariance_eq_historyXi (spectator : PrimeSource) (s l : ℕ)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedComplexCovariance C spectator s l σ τ =
      (spectatorPrior spectator (2*s)).cmean (fun ds=>
        (outerPrior C.sources (Template.current seed l) C.giant).cmean (fun x=>
          ∑ v : AllowedFrequency V l,
          ∑ c₁ : HistoryChoices C.sources seed V l,∑ c₂ : HistoryChoices C.sources seed V l,
            ((choicesMass C.sources seed V l c₁*choicesMass C.sources seed V l c₂:ℝ):ℂ)*
              C.selectedCovarianceXiTerm spectator s l σ τ ds x v c₁ c₂)) := by
  rw [selectedComplexCovariance_eq_nested]
  dsimp only
  congr 1
  funext ds
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro v hv
  exact C.selectedCoefficient_pair_eq_historyXi spectator s l σ τ ds x v

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
