import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalEnvironment

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def diagonalSingleEnergy (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) : ℝ :=
  (spectatorPrior spectator m).mean (fun ds =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mean (fun u =>
      ∑p∈integerPivotCell G,externalPivotWeight G p*
        (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mean (fun x =>
          ∑v : AllowedFrequency V l,
            diagonalSmallTerm d sources seed V giant (spectatorList spectator ds) l p u (x,v)*
              ‖diagonalCoefficientTerm d sources seed V giant X G bins (spectatorList spectator ds) l p u (x,v)‖^2)))

theorem diagonalSingleEnergy_nonneg (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) :
    0≤diagonalSingleEnergy d sources seed V giant spectator m X G bins l := by
  apply FinitePrior.mean_nonneg
  intro ds
  apply FinitePrior.mean_nonneg
  intro u
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg (externalPivotWeight_nonneg G p)
  apply FinitePrior.mean_nonneg
  intro x
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (diagonalSmallMultiplier_nonneg _ _ _ _ _) (sq_nonneg _)

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

def selectedDiagonalSingleEnergy (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) : ℝ :=
  diagonalSingleEnergy d C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (Conclusion.frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
    (Arithmetic.sourceStateBins (Conclusion.bulkSize k L/2) s C.bulkBin C.spectatorBin) l

theorem selectedDiagonalSingleEnergy_nonneg (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) :
    0≤C.selectedDiagonalSingleEnergy spectator s X l := diagonalSingleEnergy_nonneg _ _ _ _ _ _ _ _ _ _ _

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
