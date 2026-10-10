import OAI.Combinatorics.Progressions.Probability.AllocatedAccuracyReferenceMass
import OAI.Combinatorics.Progressions.Probability.AllocatedRecenteredDensityMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (modulus : ℕ)
variable (f : ((Σ a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a}, O a.val.1) → ℝ) → ℝ)
variable (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)

variable (X : Type*) [Fintype X] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)))))
variable (wholeReference : ((PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S)))))
variable (N : X → ℕ) {W τ ξ : ℝ} (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)

variable (g : ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S)))) → EuclideanJetLayers U O → ℝ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hσ1 : ∀ j, σ j ≤ 1) (Cchart : Fin m → ℝ) (hCchart : ∀ j, 0 ≤ Cchart j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cchart j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cchart 1 j)
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
      (allocatedPhysicalCubeDirections B U b S x w) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

include hperiod hσ1 hCchart hchart hsmall hg hg0 hlaw in
theorem allocatedRecenteredMaskedMass_of_density
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (residue : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) →
      ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hRefined : 0 < ((residueRefinedPeriod modulus q)))
    (hlengths : ∀ t, (Fintype.card (Fin dim) + 1) * ((residueRefinedPeriod modulus q)) ≤ principalAxisLength (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)) t)
    (href : ∀ u r, principalResidueLabel ((residueRefinedPeriod modulus q)) (reference u r) = r)
    (hresidue : ∀ u r v,
      (allocatedLongResidueWeights B U b S ((residueRefinedPeriod modulus q)) hRefined r hlengths).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j)
    (η Ecoeff Eideal : ℝ)
    (profileError : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → EuclideanJetLayers U O → ℝ)
    (hpoint : ∀ u r z,
      |(allocatedLongResidueWeights B U b S ((residueRefinedPeriod modulus q)) hRefined r hlengths).mean
        (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
          allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) z| ≤ η)
    (hprofile : ∀ u r z,
      |allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d u r z -
        allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u (reference u r)) modulus f z| ≤ profileError u r z)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) z)
    (hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), g y (point (physicalResidueReconstruction
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
        (allocatedPhysicalCubeDirections B U b S x y₀) base
        (boundedColumnResidueRepresentative q a) q v))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
        (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    (hcoeffMass : ∀ u r, (∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a *
      ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), allocatedRefinedReferenceErrorProfile B U b hR hσ S x rows X modulus q reference hb o bW d η
        u r (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim) B U b S X modulus q wholeReference x base u r a.val v))) /
          ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))) ≤ Ecoeff)
    (hidealMass : ∀ u r, (∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a *
      ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), profileError u r (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
        B U b S X modulus q wholeReference x base u r a.val v))) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))) ≤ Eideal) :
    (((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) ((allocatedPrincipalSides B U b S))
  (allocatedPrincipalSides_pos B U b S)))).mean (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point
      (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ))) ≤
      coarseReferenceMassConstant dim X W S.value + Ecoeff + Eideal ∧
    ∀ {P D Z : ℝ}, 0 ≤ P → ((dim + 1 : ℕ) : ℝ) ≤ P → (Fintype.card X : ℝ) ≤ P →
      D ≤ Real.exp P → W ≤ D * S.value → 0 < Z → Z⁻¹ ≤ 2 →
      Ecoeff + Eideal ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
        (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X →
      (((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) ((allocatedPrincipalSides B U b S))
  (allocatedPrincipalSides_pos B U b S)))).mean (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point
        (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ))) / Z ≤
          Real.exp (coefficientErrorVolumeLog P + 4) := by
  let error := fun u r z =>
    allocatedRefinedReferenceErrorProfile B U b hR hσ S x rows X modulus q reference hb o bW d η u r z +
      profileError u r z
  have hcompare (u : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S))))) (r : ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q))))) (z : EuclideanJetLayers U O) :
      |(allocatedLongResidueWeights B U b S ((residueRefinedPeriod modulus q)) hRefined r hlengths).mean
        (fun v => g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) z) -
        allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u (reference u r)) modulus f z| ≤ error u r z := by
    have hbefore := allocatedPhysicalDensityFamily_refined_comparison B U b hR hσ S x u rows s hA
      hb o hσ1 Cchart hCchart hchart hsmall bW d μ ν
      (fun v => g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v))
      (fun v => hg _) (fun v => hg0 _) (fun v => hlaw _)
      ((residueRefinedPeriod modulus q)) hRefined r hlengths (reference u r) (href u r)
      modulus ⟨∏ t, q t, rfl⟩ hperiod (residue u r) (hresidue u r) (hpoint u r) z
    exact (abs_sub_le _ (allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q
      reference residue hb o bW d u r z) _).trans (add_le_add hbefore (hprofile u r z))
  have htail (u : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S))))) (r : ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q))))) :
      (∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a *
        ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), error u r (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
          B U b S X modulus q wholeReference x base u r a.val v))) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))) ≤ Ecoeff + Eideal := by
    simp only [error, Finset.sum_add_distrib, add_div, mul_add]
    exact add_le_add (hcoeffMass u r) (hidealMass u r)
  have h := allocatedRecenteredMaskedMass_of_comparison B U b hR hσ S x rows hb o bW d modulus f hperiod
    X q reference wholeReference N base cells point href
    (fun r => allocatedLongResidueWeights B U b S ((residueRefinedPeriod modulus q)) hRefined r hlengths) g error
    hW hτ hξ hN hq hmass (Ecoeff + Eideal) hg0 hcompare hprojected htail
  refine ⟨h.trans_eq (by ring), ?_⟩
  intro P D Z hP hdim hX hD hWD hZ hZi hErrors
  exact referenceProxyMass_exp_bound dim X hP hdim hX (by exact_mod_cast S.positive)
    hW hD hWD hZ hZi (div_le_div_of_nonneg_right h hZ.le) hErrors

end Erdos3.VectorPolynomial

end

end OAI
