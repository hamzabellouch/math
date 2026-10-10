import OAI.Combinatorics.Progressions.Estimates.AllocatedGenuineCoverFromRaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
attribute [local instance 2000] fullBooleanRowSetFintype

variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

section FixedScale

variable {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

def AllocatedOriginalMeshForSampler
    (S : LayerSamplerScale (G := G) B U b R σ)
    (lengthLog Pbase Q Psp E pNum : ℝ) (δ : ℝ≥0) (A K : ℕ) : Prop :=
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 2) W / 4
    ∀ (small : ℝ) (_hsmall : 0 < small) (_hsmallMesh : small ≤ mesh)
    {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + K) ^ K) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      allocatedWholeIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference hb o bW d
        N hW small base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z δ‖ ≤
      Real.exp (-E)

def AllocatedOriginalSupportedMeshAtScale (D Psp E e pNum p₁ wCover vCover : ℝ) (δ : ℝ≥0)
    (A T Kproj Kideal Kcover : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 1 + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Q := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l F
  let K := max T (max Kproj Kideal)
  let Pjoined := max Q (max p₁ (max (Psp ^ 2)
    (max (allocatedSiteErrorFourierOutput m p₁ wCover vCover)
      (allocatedOriginalGeometryLog m Psp p₁ wCover vCover (E + 1)))))
  let Kjoined := max K Kcover
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    ∀ (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S refined) →
        AllocatedResidueSiteWitness (dim := dim) B U b S refined r.val)
      (_hcontract : AllocatedSourceCoverContract.{uG,uI,uB,uGeom,uCover,uSpace}
        B U b hR hσ S q modulus witnesses o p₁ wCover vCover e E Psp)
      [CompactSpace (CoefficientTorus (K := Fin dim) U)]
      [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
      [BorelSpace (CoefficientTorus (K := Fin dim) U)]
      (μsmall : Measure (CoefficientTorus (K := Fin dim) U))
      [μsmall.IsAddLeftInvariant] [IsProbabilityMeasure μsmall],
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 1 + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 1 + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp (E + 1 + 2) W / 4
    let small := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ wCover vCover (E + 1))
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pjoined + Kjoined) ^ Kjoined) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pjoined + Kjoined) ^ Kjoined) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets δ
    let reference₀ := allocatedSupportedWholeReference (dim := dim) B U b S refined
    let point := physicalCubeRowSample (O := rowTypes) U d rows poly hmem
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q reference₀ x base
    let weight := allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q reference₀ x hMk selection hx
      N hW small base cells (physicalCubeSiteTest test)
    let H := trimmedSpatialRootScale τ N q
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E)

omit [DecidableEq G] in
theorem allocatedOriginalSupportedMesh_budgets
    {D Psp E e pNum p₁ wCover vCover : ℝ} {A T Kproj Kideal Kcover : ℕ}
    (hD : 0 ≤ D) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hpNum : 0 ≤ pNum)
    (hpNum₁ : pNum ≤ p₁) (hPsp₁ : Psp ≤ p₁) (hT : 2 ≤ T) (hKcover : 2 ≤ Kcover) :
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 1 + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Q := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l F
  let K := max T (max Kproj Kideal)
  let Pjoined := max Q (max p₁ (max (Psp ^ 2)
    (max (allocatedSiteErrorFourierOutput m p₁ wCover vCover)
      (allocatedOriginalGeometryLog m Psp p₁ wCover vCover (E + 1)))))
  let Kjoined := max K Kcover
  0 ≤ Pjoined ∧ Psp ≤ Pjoined ∧ pNum ≤ Pjoined ∧ Psp ^ 2 ≤ Pjoined ∧
    allocatedSiteErrorFourierOutput m p₁ wCover vCover ≤ Pjoined ∧
    allocatedOriginalGeometryLog m Psp p₁ wCover vCover (E + 1) ≤ Pjoined ∧
    (Q + K) ^ K ≤ (Pjoined + Kjoined) ^ Kjoined ∧
    (Pjoined + Kcover) ^ Kcover ≤ (Pjoined + Kjoined) ^ Kjoined := by
  intro w error gainLog lengthLog Pbase l F Q K Pjoined Kjoined
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hD hPsp (by linarith)
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hD hPsp hw
  have hlength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hD hpNum he hw herror
    exact h.2.1.trans h.2.2.2.2.2
  have hF : 0 ≤ F := allocatedProfileFourierOutput_nonneg
    (allocatedActualProfileInput_bounds m hD hpNum he hgain hlength).1
  have hPbase : 0 ≤ Pbase := zero_le_one.trans
    (allocatedIdealSourceBudget_bounds m hD hpNum he hw herror).1
  have hl : 0 ≤ l := allocatedSpatialLateLog_nonneg (G := G) B hPbase hPbase
  have hQ : 0 ≤ Q := zero_le_one.trans
    (allocatedSourceSamplingBudget_bounds m dim A hPbase (by linarith) hl hF).1
  have hQjoined : Q ≤ Pjoined := le_max_left _ _
  have hpjoined : p₁ ≤ Pjoined := (le_max_left _ _).trans (le_max_right _ _)
  have hPjoined : 0 ≤ Pjoined := hQ.trans hQjoined
  have hPspJoined : Psp ≤ Pjoined := hPsp₁.trans hpjoined
  have hpNumJoined : pNum ≤ Pjoined := hpNum₁.trans hpjoined
  have hSquareJoined : Psp ^ 2 ≤ Pjoined :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hFourierJoined : allocatedSiteErrorFourierOutput m p₁ wCover vCover ≤ Pjoined :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hGeometryJoined : allocatedOriginalGeometryLog m Psp p₁ wCover vCover (E + 1) ≤ Pjoined :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hK : 1 ≤ K := (show 1 ≤ T by omega).trans (le_max_left _ _)
  have hSourceCut : (Q + K) ^ K ≤ (Pjoined + Kjoined) ^ Kjoined :=
    (pow_le_pow_left₀ (by positivity) (add_le_add hQjoined le_rfl) K).trans
      (shifted_power_self_mono hPjoined hK (le_max_left _ _))
  have hCoverCut : (Pjoined + Kcover) ^ Kcover ≤ (Pjoined + Kjoined) ^ Kjoined :=
    shifted_power_self_mono hPjoined (by omega) (le_max_right _ _)
  exact ⟨hPjoined, hPspJoined, hpNumJoined, hSquareJoined, hFourierJoined,
    hGeometryJoined, hSourceCut, hCoverCut⟩

theorem allocatedOriginalResidueWeightedMeshAtScale_supported
    {D Psp E e pNum p₁ wCover vCover : ℝ} {δ : ℝ≥0} {A T Kproj Kideal Kcover : ℕ}
    (hD : 0 ≤ D) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hpNum : 0 ≤ pNum)
    (hp₁ : 0 ≤ p₁) (hwCover : 0 ≤ wCover) (hvCover : 0 ≤ vCover)
    (hpNum₁ : pNum ≤ p₁) (hPsp₁ : Psp ≤ p₁)
    (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p₁)
    (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hT : 2 ≤ T) (hKcover : 2 ≤ Kcover)
    (hSampling : AllocatedBooleanRowsSampling.{uSpace,uGeom,uG,uI,uB,uCover}
      m dim Kcover rowTypes rows)
    (horiginal : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp (E + 1) e pNum δ A T Kproj Kideal) :
    AllocatedOriginalSupportedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp E e pNum p₁ wCover vCover δ A T Kproj Kideal Kcover := by
  unfold AllocatedOriginalSupportedMeshAtScale
  intro w error gainLog S lengthLog Pbase l F Q K Pjoined Kjoined
  have hraw : AllocatedOriginalMeshForSampler.{uG,uI,uB,uGeom,uCover,uSpace}
      (dim := dim) B U b hR hσ S lengthLog Pbase Q Psp (E + 1) pNum δ A K := horiginal
  clear horiginal
  have horiginal := hraw
  clear hraw
  obtain ⟨hPjoined, hPspJoined, hpNumJoined, hSquareJoined, hFourierJoined,
    hGeometryJoined, hSourceCut, hCoverCut⟩ :=
    allocatedOriginalSupportedMesh_budgets (G := G) (dim := dim) B
      (A := A) (Kproj := Kproj) (Kideal := Kideal) (wCover := wCover) (vCover := vCover)
      hD hPsp hE he hpNum hpNum₁ hPsp₁ hT hKcover
  obtain ⟨hS, horiginal⟩ := horiginal
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, horiginal⟩ := horiginal x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusSize hspatialPeriod hcoefficientPeriod
  obtain ⟨s, hA, hinverse, horiginal⟩ := horiginal modulus hmodulus
    hmodulusSize hspatialPeriod hcoefficientPeriod
  refine ⟨s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, horiginal⟩ :=
    horiginal block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro witnesses hcontract _ _ _ μsmall _ _ W hW indices ξ hξ sourceMesh small τ hτ hτP
    N hN hsizeN poly hpoly hmem rank hrank hRank base cells hcells test htest Z hZ
    f reference₀ point law target reconstruct weight H V₀
  have hsourceMesh : 0 < sourceMesh := by
    have ht : 0 < normalizedTupleTolerance X Psp (E + 1 + 2) :=
      (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
        (Real.exp_nonneg _) (half_pos (Real.exp_pos _))).1
    have hLip := anisotropicSpatialDensityLip_nonneg selection (show 0 ≤ 1 / (Mk : ℝ) by positivity)
    exact div_pos (twoTermErrorWidth_spec (by positivity) ht).1 (by norm_num)
  have hcoverMesh := (allocatedOriginalCoverMesh_spec m hPsp hp₁ hwCover hvCover (by linarith : 0 ≤ E + 1)).1
  have hsmallPos : 0 < small := lt_min hsourceMesh hcoverMesh
  obtain ⟨hmass, hsource⟩ := horiginal small hsmallPos (min_le_left _ _) hτ hτP N hN
    (fun t => (Real.exp_le_exp.mpr hSourceCut).trans (hsizeN t)) poly hpoly hmem hrank
    ((Real.exp_le_exp.mpr hSourceCut).trans hRank) base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hXJoined : (Fintype.card X : ℝ) ≤ Pjoined := hXPsp.trans hPspJoined
  have hdimJoined : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pjoined := by
    apply le_trans _ hSquareJoined
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_two]
    have hd : (dim : ℝ) + 1 ≤ Psp := by exact_mod_cast hdimSp
    exact mul_le_mul hd hXPsp (Nat.cast_nonneg _) hPsp
  let Prows (O : Fin m → Type) [∀ j, Fintype (O j)] (values : ∀ j, O j → Finset (Fin dim)) : Prop :=
    ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (values j)).mulVecLin.range
  have hperiod : Prows rowTypes rows :=
    boundedBooleanJetRows_family_transport (fun j : Fin m => j.val + 1) Prows hcoefficientPeriod
      (fun j => fullBooleanRowSetFintype dim (j.val + 1))
  have hWscale : W ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hZi : Z⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hZpos).2 (by linarith)
  exact hcontract sourceMesh hsourceMesh hKcover hSampling δ hδ hδe hRi
    x hb bW d hperiod C V hC hV
    (fun j => (hCp j).trans (Real.exp_le_exp.mpr hpNum₁))
    (fun j => (hVp j).trans (Real.exp_le_exp.mpr hpNum₁))
    hPjoined hXJoined hdimJoined hFourierJoined hGeometryJoined μsmall ν poly hpoly hmem
    (Real.exp_nonneg Psp) (Real.exp_le_exp.mpr hPspJoined) hτ
    (hτP.trans (Real.exp_le_exp.mpr hpNumJoined)) hqPsp N
    (fun t => (Real.exp_le_exp.mpr hCoverCut).trans (hsizeN t)) hrank
    ((Real.exp_le_exp.mpr hCoverCut).trans hRank) W hW
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) hvarsGrowth hWscale
    base cells ξ hξ hmass Mk hMk hMkPsp selection hx le_rfl
    (hspatialPeriod (fun g => (0 : ℤ) + (x g none : ℤ))) reference href
    (physicalCubeSiteTest test) (physicalCubeSiteTest_norm_le test htest) Z hZpos hZi hsource

end FixedScale

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

def AllocatedCommonSupportedMeshAt (p Psp E e t : ℝ) (δ : ℝ≥0)
    (A T Kproj Kideal Kcover : ℕ) : Prop :=
  ∀ {c : ℝ} (_hc : 0 ≤ c) {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t) (_hR1 : ∀ j, R j ≤ 1)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c),
    let p₁ := allocatedCommonRefinedSourceLog m p c Psp e (E + 1 + 4)
      (allocatedOriginalCoverAccuracy Psp (E + 1))
    let w := allocatedSiteKernelMaskLog m Psp
    let v := allocatedIdealProfileLog m p₁ e
    AllocatedOriginalSupportedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ (allocatedComparisonDimension m p) Psp E e
      (allocatedCommonScaleNumeric m p c Psp (E + 1 + 4)) p₁ w v δ A T Kproj Kideal Kcover

theorem allocatedCommonResidueWeightedOriginalMeshAt_supported
    {p Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hT : 2 ≤ T)
    (horiginal : AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B p Psp (E + 1) e t δ A T Kproj Kideal) :
    ∃ Kcover : ℕ, 2 ≤ Kcover ∧
      AllocatedCommonSupportedMeshAt.{uG,uI,uB,uGeom,uCover,uSpace}
        (G := G) (dim := dim) B p Psp E e t δ A T Kproj Kideal Kcover := by
  obtain ⟨Kcover, hKcover, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uSpace,uGeom,uG,uI,uB,uCover} m dim
  refine ⟨Kcover, hKcover, ?_⟩
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi p₁ w v
  have hraw : 0 ≤ E + 1 + 4 := by linarith
  have hsite : 0 ≤ allocatedOriginalCoverAccuracy Psp (E + 1) := by
    have hsp := coefficientErrorSpatialLog_nonneg hPsp
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hp₁, _, _, hc₁, hPsp₁, _, _, _, _, hpNum₁, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hc hPsp he hraw hsite
  have hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp := by
    apply le_trans _ hmPsp
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp :=
    (hvars.trans hpPsp).trans (by linarith [Real.add_one_le_exp Psp])
  exact allocatedOriginalResidueWeightedMeshAtScale_supported B U b hR hσ
    (allocatedComparisonDimension_bounds m hp).1 hPsp hE he
    (allocatedCommonScaleNumeric_bounds m hp hc hPsp hraw).1 hp₁
    (allocatedSiteKernelMaskLog_nonneg m hPsp) (allocatedIdealProfileLog_nonneg m hp₁ he)
    hpNum₁ hPsp₁ hdimSp hvarsGrowth (fun j => (hRi j).trans (Real.exp_le_exp.mpr hc₁))
    hδ hδe hT hKcover (hSampling (fun j => fullBooleanRowSetFintype dim (j.val + 1)))
    (horiginal hc U b hR hσ hσt hR1 hRi hσi)

end Erdos3.VectorPolynomial

end

end OAI
