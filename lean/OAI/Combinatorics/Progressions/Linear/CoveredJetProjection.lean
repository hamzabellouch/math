import OAI.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ}
variable {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] in
theorem euclideanCoefficientJetMap_cover (d : ℕ) (x : CoefficientTorus (K := K) U) :
    euclideanCoefficientJetMap U root A rows
        (quotientIntegerCover (coefficientIntegerLattice U) d x) =
      d • euclideanCoefficientJetMap U root A rows x :=
  map_nsmul (euclideanCoefficientJetMap U root A rows) d x

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

theorem coefficientCover_density_map (d : ℕ) (hd : 0 < d)
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D) (hi : Integrable D μ)
    (h0 : ∀ x, 0 ≤ D x) :
    (realDensityMeasure μ (fun x => D (quotientIntegerCover (coefficientIntegerLattice U) d x))).map
        (quotientIntegerCover (coefficientIntegerLattice U) d) = realDensityMeasure μ D :=
  measurePreserving_realDensity_map μ μ _ (coefficientCover_measurePreserving U μ d hd) D hD hi h0

theorem coveredEuclideanJet_density_projection (d : ℕ) (hd : 0 < d)
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D) (hi : Integrable D μ)
    (h0 : ∀ x, 0 ≤ D x) (ξ : Measure (EuclideanJetLayers U O))
    (f : EuclideanJetLayers U O → ℝ)
    (hlaw : (realDensityMeasure μ
      (fun x => D (quotientIntegerCover (coefficientIntegerLattice U) d x))).map
        (euclideanCoefficientJetMap U root A rows) = realDensityMeasure ξ f) :
    (realDensityMeasure ξ f).map (fun z => d • z) =
      (realDensityMeasure μ D).map (euclideanCoefficientJetMap U root A rows) := by
  have hF := (euclideanCoefficientJetMap_continuous U root A rows).measurable
  have hC := (quotientIntegerCover_continuous (coefficientIntegerLattice (K := K) U) d).measurable
  have hn : Measurable (fun z : EuclideanJetLayers U O => d • z) :=
    (continuous_id.nsmul d).measurable
  rw [← hlaw, Measure.map_map hn hF]
  have he : (fun z : EuclideanJetLayers U O => d • z) ∘ euclideanCoefficientJetMap U root A rows =
      euclideanCoefficientJetMap U root A rows ∘ quotientIntegerCover (coefficientIntegerLattice U) d :=
    funext (fun x => (euclideanCoefficientJetMap_cover U root A rows d x).symm)
  rw [he, ← Measure.map_map hF hC, coefficientCover_density_map U μ d hd D hD hi h0]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem coveredCanonicalJet_density_projection
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (d : ℕ) (hd : 0 < d) (ξ : Measure (EuclideanJetLayers U O)) (f : EuclideanJetLayers U O → ℝ)
    (hlaw : (realDensityMeasure μ (fun x => canonicalCoefficientDensity U b hb o c w p
      (quotientIntegerCover (coefficientIntegerLattice U) d x))).map
        (euclideanCoefficientJetMap U root A rows) = realDensityMeasure ξ f) :
    (realDensityMeasure ξ f).map (fun z => d • z) =
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).map
        (fun x j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j)
          (canonicalCoefficientJetArrays root A rows x j)) := by
  have hi := (canonicalCoefficientDensity_mass U b hb o c w p μ ν hw hs).1
  exact (coveredEuclideanJet_density_projection U root A rows μ d hd
    (canonicalCoefficientDensity U b hb o c w p)
    (canonicalCoefficientDensity_measurable U b hb o c w p) hi
    (canonicalCoefficientDensity_nonneg U b hb o c w p hw) ξ f hlaw).trans
      (canonicalCoefficientJetArrays_quotient_law U b hb o root A rows μ ν c w p hw hs).symm

end Erdos3.VectorPolynomial

end

end OAI
