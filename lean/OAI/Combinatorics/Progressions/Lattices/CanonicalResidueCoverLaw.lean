import OAI.Combinatorics.Progressions.Probability.CanonicalCoverLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K R : Type*} [Fintype K] [Fintype R] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientResidueCoverLaw
    (bL : Basis R ℤ (coefficientIntegerLattice (K := K) U))
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (d : ℕ) [NeZero d] :
    ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure).map
        (fun x => canonicalCoefficientCoverLift U b hb o d x.1 +
          (coverKernelBasisEquiv (coefficientIntegerLattice (K := K) U) bL d
            (Nat.pos_of_ne_zero (NeZero.ne d)) x.2).val) =
      realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let _ := coefficientCoverKernelFintype (K := K) U d hd
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  let : IsProbabilityMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    Measure.pi.instIsProbabilityMeasure _
  rw [finiteKernelLiftLaw_basisResidues (coefficientIntegerLattice (K := K) U) bL d
    _ _ (canonicalCoefficientCoverLift_measurable U b hb o d)]
  exact canonicalCoefficientCoverLaw U b hb o μ ν c w p hw hs d hd

end Erdos3.VectorPolynomial

end

end OAI
