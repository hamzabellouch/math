import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularMellin
import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeHeight

namespace OAI

/-! Actual semiprime coordinates as a uniform smooth prime-weight family.
The angular factor remains separate from the radial weight throughout. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

abbrev SemiprimeAngularWeightParameters :=
  (Ici (0:ℝ) × Ici (1:ℝ)) × (Ici (0:ℝ) × Ici (1:ℝ))

def semiprimeAngularLeftLength (z : SemiprimeAngularWeightParameters) : ℝ := z.1.2

def semiprimeAngularRightLength (z : SemiprimeAngularWeightParameters) : ℝ := z.2.2

def semiprimeAngularLeftWeight (z : SemiprimeAngularWeightParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.1.1

def semiprimeAngularRightWeight (z : SemiprimeAngularWeightParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.2.1

def semiprimeAngularLeftLogWeights :
    LogarithmicWeightFamily
      (fun z : SemiprimeAngularWeightParameters × Unit => semiprimeAngularLeftLength z.1)
      (fun z => semiprimeAngularLeftWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiprimeAngularLeftLength
    (fun z => semiprimeSmoothWeight z.1.1) (fun z => z.1.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeAngularWeightParameters => z.1.1))

def semiprimeAngularRightLogWeights :
    LogarithmicWeightFamily
      (fun z : SemiprimeAngularWeightParameters × Unit => semiprimeAngularRightLength z.1)
      (fun z => semiprimeAngularRightWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiprimeAngularRightLength
    (fun z => semiprimeSmoothWeight z.2.1) (fun z => z.2.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeAngularWeightParameters => z.2.1))

def semiprimeAngularUnitPolynomial (ℓ : ℤ) (r s A B u : ℝ) : ℂ :=
  productGaussPolynomial
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B)) ℓ u

lemma semiprimeAngularGaussPolynomial_eq_unit (ℓ : ℤ) (X : ℝ) (i j : ℕ) (u : ℝ) :
    semiprimeAngularGaussPolynomial ℓ X i j u =
      semiprimeAngularUnitPolynomial ℓ
        (semiprimePartitionScale i/X^(2/5:ℝ))
        (semiprimePartitionScale j/X^(2/5:ℝ))
        (semiprimePartitionScale i) (semiprimePartitionScale j) u := by
  unfold semiprimeAngularGaussPolynomial semiprimeAngularUnitPolynomial
  rw [fullSquarefreePrimeSupport_unit,fullSquarefreePrimeSupport_unit]
  unfold productGaussPolynomial
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [fullPrimeCoefficient_unit hp,fullPrimeCoefficient_unit hq]
  rfl

end CubicFirstMoment

end

end OAI
