import OAI.Combinatorics.Progressions.Geometry.GoodPartSpatialAverage
import OAI.Combinatorics.Progressions.Probability.GeometricSelectedMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {p c e E : ℝ}
local notation "radius" => allocatedIdealCoverPrimitiveRadius m p c
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "L" => scalarSourceTransitionBound

local notation "scaleInput" => allocatedGeometryInput m p c 0 E
local notation "scaleLog" => allocatedSiteScaleLog m scaleInput e E
local notation "inputParameter" => allocatedGeometrySourceInput m p c e E
local notation "sourceParameter" => siteSourceParameter m inputParameter
local notation "maskLog" => siteSourceMaskLog m inputParameter
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S

local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "chartCap" => (NNReal.mk (Real.exp c) (Real.exp_nonneg c))
local notation "geometryQ" => Real.toNNReal (8 * (allocatedComparisonDimension m p + 1))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

local notation "samplingInput" => (fun t : ℝ => allocatedGeometricSamplingInput m p c e E t)
local notation "rankLog" => (fun (k : ℕ) (t : ℝ) => allocatedGeometricSamplingThreshold m k p c e E t)

local notation "Kernel" => (G → IntegerScalarCubeBox (Fin dim) S.value)

def AllocatedGoodPartCoverAt (K : ℕ) : Prop :=
  ∀
    (_hp : 0 ≤ p) (_hc : 0 ≤ c) (_he : 0 ≤ e) (_hE : 0 ≤ E)
    (_hdimSmall : dim ≤ m + 1)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hn₁ : ∀ j, (n j : ℝ) ≤ p)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (_hcutoff : (M₀ : ℝ) ≤ Real.exp p)
    (_hScale : S = allocatedSiteScale (G := G) B U b hR hσ scaleInput e E)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (_hRadius : ∀ j, R j = radius)
    (_hforward : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Real.exp c * ‖z‖)
    (_hinverse : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Real.exp c * ‖z‖)
    (_hvolume : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp c)
    (_hσ1 : ∀ j, σ j ≤ 1)
    (_hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) ,
    ∃ witnesses : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ sitePeriods (witnesses t r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∃ g : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        (∀ a, ((witnesses t r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ t r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * geometryQ) *
        (Real.toNNReal (Real.exp sourceParameter) * ∑ j, chartCap * Fintype.card (J j)) * commonSitePeriod (witnesses t r).expansion k)
          (4 * commonSitePeriod (witnesses t r).expansion k)) (g t r k s) ∧ ∀ z, ‖g t r k s z‖ ≤ 1) ∧
      (∀ t r, (∑ k, ‖coverSiteCoefficient (witnesses t r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      (∀ t, allocatedResidueCoverCoefficientMass B U b S (period t) (witnesses t) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      ∀ (selection : Fin dim ↪ G),
      let Good := GoodScalarKernelTuple («L» := S.value) selection (1 / (M₀ : ℝ)) M₀
      let GoodKernel := {x : Kernel // Good x}
      ∃ periodIndex : GoodKernel → Fin M₀,
        (∀ (x : GoodKernel) (root : G → ℤ),
          integerScalarLattice (Unit ⊕ Fin dim) (period (periodIndex x) : ℤ) ≤
            pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x.val) selection)
              (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x.val) selection)) ∧
        (∀ (x : GoodKernel) j, integerScalarLattice (rowTypes j) (period (periodIndex x) : ℤ) ≤
          (scalarKernelIntegerJet x.val (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ (kernelLaw : FiniteProbabilityWeights Kernel),
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
    {X : Type uX} [Fintype X] [DecidableEq X]
    {Pbase : ℝ} (_hbase : 0 ≤ Pbase) (_hn : (Fintype.card X : ℝ) ≤ Pbase)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp Pbase) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp Pbase)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp (rankLog K Pbase) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp (rankLog K Pbase) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun (x : GoodKernel) (z : Option (Fin dim) × X → ℤ) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x.val (rows) hb o bW d y₀ (period (periodIndex x)) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period (periodIndex x)))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period (periodIndex x)) (witnesses (periodIndex x)) hb o bW d (g (periodIndex x)) τ x.val p hmp
          (standardPhysicalCubeOutput z))
    let averageError := fun z => kernelLaw.complexMean
      (fun x => if hx : Good x then error ⟨x, hx⟩ z else 0)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖averageError z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (averageError z * φ z)‖ ≤ Real.exp (-E)

theorem allocatedGoodPartCoverAt_of_cover {K : ℕ} (hK : 2 ≤ K)
    (hcover : AllocatedGeometricCoverAt.{uG,uI,uB,uJ,uQ,uX} (dim := dim)
      (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (S := S) (M₀ := M₀)
      (p := p) (c := c) (e := e) (E := E) K) :
    AllocatedGoodPartCoverAt.{uG,uI,uB,uJ,uQ,uX} (dim := dim)
      (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (S := S) (M₀ := M₀)
      (p := p) (c := c) (e := e) (E := E) K := by
  intro hp hc he hE hdimSmall hvars hI hn₁ hJ hcutoff hScale hσi hRadius
    hforward hinverse hvolume hσ1 hBlocks
  obtain ⟨witnesses, hBounds, hgeometry⟩ := hcover hp hc he hE hdimSmall hvars hI hn₁ hJ hcutoff
    hScale hσi hRadius hforward hinverse hvolume hσ1 hBlocks
  refine ⟨witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _
  obtain ⟨g, hg, hcoeff, hmass, hcomparison⟩ := hgeometry hb o bW d
  refine ⟨g, hg, hcoeff, hmass, ?_⟩
  intro selection
  dsimp only
  let Good := GoodScalarKernelTuple («L» := S.value) selection (1 / (M₀ : ℝ)) M₀
  let GoodKernel := {x : Kernel // Good x}
  have hex (x : GoodKernel) := hcomparison x.val selection x.property
  choose periodIndex hspatial hperiod hcompare using hex
  refine ⟨periodIndex, hspatial, hperiod, ?_⟩
  intro kernelLaw τ hτ hτ1 hτe X _ _ Pbase hPbase hX _ _ _ μ _ _ ν _ _ polynomial hdegree hmp
    stride hstridePos R₁ S₀ ρ hS₀ hSP hρ hρP hstride H hH hrank hRlarge cells hcells W hW hwidth
  let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
  let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
  let errors := fun (x : GoodKernel) (z : Option (Fin dim) × X → ℤ) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x.val (rows) hb o bW d y₀ (period (periodIndex x)) f
          (physicalCubeRowSample U d (rows) polynomial hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period (periodIndex x)))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period (periodIndex x)) (witnesses (periodIndex x)) hb o bW d (g (periodIndex x)) τ x.val polynomial hmp
          (standardPhysicalCubeOutput z))
  have herr (x : GoodKernel) :
      selectedResidueDensityMass stride cells W (fun z => ‖errors x z‖) ≤ Real.exp (-E) := by
    have hx := hcompare x τ hτ hτ1 hτe (X := X) (Pbase := Pbase) hPbase hX
      μ ν polynomial hdegree hmp stride hstridePos hS₀ hSP hρ hρP hstride H hH hrank hRlarge
      cells hcells W hW hwidth
    exact hx.choose_spec.1
  have hnumbers := allocatedGeometricSamplingInput_mass_bounds m hp hc he hE hPbase
  have hbudget := allocatedGeometricSamplingInput_controls m hp hc he hE hPbase
  have hZ := selectedResidue_mass_of_polynomial_threshold K hK hnumbers.1 hnumbers.2 hbudget.2.1
    hρ hρP stride hstridePos (fun x => (hstride x).trans hSP) H hH cells hcells W hW hwidth
  refine ⟨hZ, ?_, ?_⟩
  · exact selectedResidue_goodPart_error kernelLaw Good stride cells W hW hZ
      (fun x hx => errors ⟨x, hx⟩) (Real.exp_pos _).le (fun x hx => herr ⟨x, hx⟩)
  · intro φ hφ
    exact selectedResidue_goodPart_test_error kernelLaw Good stride cells W hW hZ
      (fun x hx => errors ⟨x, hx⟩) (Real.exp_pos _).le (fun x hx => herr ⟨x, hx⟩) φ hφ

theorem exists_uniform_goodPart_cover (m dim : ℕ) :
    ∃ K a : ℕ, 2 ≤ K ∧ 2 ≤ a ∧
      (∀ p : ℝ, 0 ≤ p → allocatedGeometricSamplingThreshold m K p p p p p ≤ (p + a) ^ a) ∧ ∀
      {G : Type uG} [Fintype G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
      [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
      {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {p c e E : ℝ} {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      (S : LayerSamplerScale (G := G) B U b R σ) (M₀ : ℕ),
      AllocatedGoodPartCoverAt.{uG,uI,uB,uJ,uQ,uX} (dim := dim) (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ)
        (S := S) (M₀ := M₀) (p := p) (c := c) (e := e) (E := E) K := by
  obtain ⟨K, a, hK, ha, hbound, hcover⟩ := exists_uniform_geometric_cover.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨K, a, hK, ha, hbound, ?_⟩
  intro G _ I _ _ n B _ _ J _ U b p c e E R σ hR hσ S M₀
  exact allocatedGoodPartCoverAt_of_cover (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ)
    (S := S) (M₀ := M₀) (p := p) (c := c) (e := e) (E := E) hK (hcover B U b hR hσ S M₀)

end Erdos3.VectorPolynomial

end

end OAI
