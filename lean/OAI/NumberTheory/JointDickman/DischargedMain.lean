import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceDivergence
import OAI.NumberTheory.JointDickman.ConditionalMain
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import OAI.NumberTheory.JointDickman.Probability.FiniteMcDiarmidDischarge
import OAI.NumberTheory.JointDickman.Arithmetic.FiniteBinDistributionDischarge
import OAI.NumberTheory.JointDickman.Arithmetic.BrunUpperSieve
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeSelbergDelange
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterDischarge

namespace OAI

/-! # Joint distributions from progressively weaker analytic hypotheses -/
namespace JointDickman
open PublishedInputs

theorem main_results_after_mertens
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMV : MultiplicativeExponentialInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : FiniteBinDistributionInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  main_results_of_published hMR hMRT hKMT hFord hSD hSW
    primeReciprocalMertensInput primeProductMertensInput hMV hMC hBill

theorem main_results_after_elementary_inputs
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMV : MultiplicativeExponentialInput) (hBill : FiniteBinDistributionInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  main_results_after_mertens hMR hMRT hKMT hFord hSD hSW hMV
    (fun _ M => finiteMcDiarmidInput M) hBill

/-- The exact main results after the two Mertens estimates, finite
concentration, and finite-bin Dickman distribution have been proved. -/
theorem main_results_after_bin_distribution
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMV : MultiplicativeExponentialInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  main_results_after_elementary_inputs hMR hMRT hKMT hFord hSD hSW hMV
    finiteBinDistributionInput

/-- All three exact main results with the two Mertens estimates, concentration,
finite-bin distribution, and the finite-event upper sieve discharged. -/
theorem main_results_after_upper_sieve
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMV : MultiplicativeExponentialInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  main_results_after_bin_distribution hMR hMRT hKMT fordUpperSieveInput hSD hSW hMV

/-- The exact main results after the squarefree Selberg--Delange expansion
has also been proved, including every fixed order and all real cutoffs. -/
theorem main_results_after_selberg_delange
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMV : MultiplicativeExponentialInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  main_results_after_upper_sieve hMR hMRT hKMT squarefreeSelbergDelangeInput hSW hMV

/-- The exact main results after the uniform squarefree character estimate
has also been proved for both fixed exponents and every real cutoff. -/
theorem main_results_after_character_estimate
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceInput) (hMV : MultiplicativeExponentialInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw :=
  main_results_after_selberg_delange hMR hMRT hKMT squarefreeCharacterEstimateInput hMV

/-- All three exact main results using the proved qualitative character-distance
bound. The stronger numerical KMT input is no longer required. -/
theorem main_results_after_character_distance
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (_hMV : MultiplicativeExponentialInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw := by
  have hJ : JointDickmanLaw := jointDickmanLaw_of_rational_fixedScale
    (rationalFixedScaleLaw_of_distance_divergence hMR hMRT characterDistanceDivergence
      fordUpperSieveInput squarefreeSelbergDelangeInput squarefreeCharacterEstimateInput
      primeReciprocalMertensInput primeProductMertensInput
      (fun _ M => finiteMcDiarmidInput M) finiteBinDistributionInput)
  exact ⟨hJ,increasingOrderLaw_of_jointDickmanLaw hJ,decreasingOrderLaw_of_jointDickmanLaw hJ⟩

/-- The exact joint law and both ordering laws after the necessary
Montgomery--Vaughan minor-arc special case has been proved. -/
theorem main_results_after_exponential_sums
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw := by
  have hJ : JointDickmanLaw := jointDickmanLaw_of_rational_fixedScale
    (rationalFixedScaleLaw_of_distance_divergence hMR hMRT characterDistanceDivergence
      fordUpperSieveInput squarefreeSelbergDelangeInput squarefreeCharacterEstimateInput
      primeReciprocalMertensInput primeProductMertensInput
      (fun _ M => finiteMcDiarmidInput M) finiteBinDistributionInput)
  exact ⟨hJ,increasingOrderLaw_of_jointDickmanLaw hJ,decreasingOrderLaw_of_jointDickmanLaw hJ⟩

end JointDickman

end OAI
