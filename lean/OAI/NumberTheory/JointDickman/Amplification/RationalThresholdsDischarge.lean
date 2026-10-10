import OAI.NumberTheory.JointDickman.Amplification.RationalThresholds
import OAI.NumberTheory.JointDickman.Arithmetic.RationalBinSmoothDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem rationalFixedScaleLaw_of_distance_divergence_proved
    (hKMT : CharacterDistanceDivergence) (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (hMP : PublishedInputs.PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, PublishedInputs.FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : PublishedInputs.FiniteBinDistributionInput) : RationalFixedScaleLaw := by
  intro c d hc hc1 hd hd1
  obtain ⟨J,k,l,hJ,hk,hkj,hl,hlj,hce,hde⟩ := rational_common_denominator hc hc1 hd hd1
  rw [hce,hde]
  exact fixedDensity_common_denominator_proved hKMT hFord hSD hSW hM hMP hMC hBill hJ hk hkj hl hlj

theorem rationalFixedScaleLaw_of_published_proved
    (hKMT : PublishedInputs.CharacterDistanceInput) (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (hMP : PublishedInputs.PrimeProductMertensInput)
    (_hMV : PublishedInputs.MultiplicativeExponentialInput)
    (hMC : ∀ B M : ℕ, PublishedInputs.FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : PublishedInputs.FiniteBinDistributionInput) : RationalFixedScaleLaw :=
  rationalFixedScaleLaw_of_distance_divergence_proved
    (characterDistanceDivergence_of_published hKMT) hFord hSD hSW hM hMP hMC hBill

end JointDickman

end OAI
