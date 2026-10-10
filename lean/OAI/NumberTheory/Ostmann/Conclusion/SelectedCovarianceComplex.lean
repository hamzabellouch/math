import OAI.NumberTheory.Ostmann.Conclusion.ActualCovarianceComplex
import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Conclusion
open Construction

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

def selectedComplexCovariance (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s l : ℕ)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) : ℂ :=
  actualComplexPermutationCovariance C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) C.scale C.giantCenter
    (residueTransform d) (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l
    (selectedLeafPermutation C l) (selectedLeafPermutation_source C l) a b

@[simp] theorem selectedComplexCovariance_re (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s l : ℕ)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    (selectedComplexCovariance C spectator s l a b).re=selectedCovariance C spectator s l a b :=
  actualComplexPermutationCovariance_re _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem selectedCovariance_le_of_complex_norm (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s l : ℕ)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    {B : ℝ} (hB : ‖selectedComplexCovariance C spectator s l a b‖ ≤ B) :
    selectedCovariance C spectator s l a b ≤ B := by
  rw [← selectedComplexCovariance_re]
  exact (Complex.re_le_norm _).trans hB

theorem selectedComplexCovariance_eq_nested
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (s l : ℕ)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedComplexCovariance C spectator s l a b=
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let T := Template.current seed l
      let V := frequencyBound Bs BD Bz k L
      let bins := Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin
      (spectatorPrior spectator (2*s)).cmean (fun ds =>
        (outerPrior C.sources T C.giant).cmean (fun x =>
          ∑ v : AllowedFrequency V l,
            actualCoefficient C.sources seed V C.scale C.giantCenter (residueTransform d) bins
              (spectatorList spectator ds) l
              (outerState C.sources T C.giant (x.1,x.2.1,
                sourceAssignmentPermutation C.sources T (selectedLeafPermutation C l a)
                  (selectedLeafPermutation_source C l a) x.2.2) v.val) *
            conj (actualCoefficient C.sources seed V C.scale C.giantCenter (residueTransform d) bins
              (spectatorList spectator ds) l
              (outerState C.sources T C.giant (x.1,x.2.1,
                sourceAssignmentPermutation C.sources T (selectedLeafPermutation C l b)
                  (selectedLeafPermutation_source C l b) x.2.2) v.val)))) := by
  simp only [selectedComplexCovariance,actualComplexPermutationCovariance,amplitudePrior,
    FinitePrior.pair_cmean,actualCoefficientRow,amplitudeSamplePermutation,
    Equiv.prodCongr_apply]
  rfl

end Ostmann.Conclusion

end

end OAI
