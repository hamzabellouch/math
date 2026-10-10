import OAI.NumberTheory.DukePrimeDegree.Geometry.CanonicalRootBasic
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCoefficientReduction

namespace OAI

/-! # Canonical coefficients applied to the published entropy formula -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The canonical root entropy identity of EKL (2006), Proposition 3.1(3). -/
def CanonicalRootEntropyFormula : Prop :=
  ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0),
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1)) =
      ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) ell)

/-- The canonical entropy formula, together with the elementary coefficient
properties, gives root entropy coefficients. -/
def canonicalRootEntropyCoefficients (hformula : CanonicalRootEntropyFormula d μ) :
    RootEntropyCoefficients d μ where
  coefficient := canonicalRootCoefficient d μ
  diagonal_zero := canonicalRootCoefficient_diagonal d μ
  nonneg := canonicalRootCoefficient_nonneg d μ
  zero_iff := canonicalRootCoefficient_zero_iff d μ hA
  one_of_invariant := canonicalRootCoefficient_one_of_invariant d μ hA
  entropy_formula := hformula

/-- The canonical entropy formula forces the coefficients to be zero or one. -/
theorem canonicalRootCoefficient_zero_or_one
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hd : 2 < d + 1) (hformula : CanonicalRootEntropyFormula d μ)
    (i j : Fin (d + 1)) :
    canonicalRootCoefficient d μ i j = 0 ∨ canonicalRootCoefficient d μ i j = 1 :=
  (canonicalRootEntropyCoefficients d μ hA hformula).zero_or_one hd i j

/-- The canonical entropy formula turns positive metric entropy into
invariance under a root subgroup. -/
theorem exists_invariant_root_of_canonical_entropy_formula
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hd : 2 < d + 1) (hformula : CanonicalRootEntropyFormula d μ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (hpos : 0 < measureEntropy μ
      (fun x => rightAction x (diagonalOneParameter ell hell 1))) :
    ∃ (i j : Fin (d + 1)) (hij : i ≠ j), ∀ t : ℝ,
      μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) = μ :=
  (canonicalRootEntropyCoefficients d μ hA hformula).exists_invariant_root_of_entropy_pos
    hd ell hell hpos

end DukePrimeDegree

end

end OAI
