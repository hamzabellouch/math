import OAI.NumberTheory.JointDickman.Analysis.CanonicalMellinEnergy
import OAI.NumberTheory.JointDickman.Analysis.MellinRestrictionRestore

namespace OAI

/-! # Restoring the full coefficient in the canonical frequency partition -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem canonical_full_energy {P Q η : ℝ} {J N : ℕ} (hJ : 0 < J)
    (hPbig : 2*Real.exp 1 ≤ P) (hP : 2 ≤ Real.log P) (hPQ : P ≤ Q)
    (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N)
    (hupper : ∀ j ∈ range J, 2*mrtBandUpper Q (j+1) ≤ N)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hb : ∀ n, ‖F n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
      4*(∫ t in S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
        ((canonicalMellinBands P Q η).polynomial F) (canonicalMellinBands P Q η).threshold J,
        ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2)+
      2*(2816*Real.exp 1*(T/N+1)*(8/P+4/(mrtBaseResolution P Q η))+
        1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹+2*(T/N+1)/P)+
      48*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card:ℝ)/N := by
  classical
  let E := mrtTypical (range J) (canonicalMellinBands P Q η).primes
  let R := S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
    ((canonicalMellinBands P Q η).polynomial F) (canonicalMellinBands P Q η).threshold J
  have hr := angularMellin_energy_of_restriction E F hb hN hT hS
  have hm := angularMellin_restriction_energy E F hb hN hT
    (Set.inter_subset_left.trans hS : R ⊆ Set.Ioc (-T) T)
  have hc := canonical_mellin_energy_bound hJ hPbig hP hPQ hη hη' hbudget hH hN hupper
    F hF (fun n _ => hb n) hT hSm hS
  change (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
    2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes F) t‖^2)+_ at hr
  change (∫ t in R, ‖angularMellinPolynomial (Ioc N (2*N))
    (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes F) t‖^2) ≤ _ at hm
  dsimp only [E,R] at hr hm
  linear_combination hr + 2*hm + 2*hc

end JointDickman

end OAI
