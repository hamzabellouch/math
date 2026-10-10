import OAI.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedGeometricSamplingInput {A : Type*} [Semiring A]
    (m : ℕ) (p c e E t : A) : A :=
  let q := allocatedGeometrySourceInput m p c e E
  let u := siteSourceParameter m q
  (m + 2 : ℕ) * (t + 1) +
    allocatedSiteErrorFourierOutput m u (siteSourceMaskLog m q) (allocatedIdealProfileLog m u e)

theorem allocatedGeometricSamplingInput_controls (m : ℕ) {p c e E t : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E) (ht : 0 ≤ t) :
    let q := allocatedGeometrySourceInput m p c e E
    let u := siteSourceParameter m q
    let P := allocatedGeometricSamplingInput m p c e E t
    0 ≤ P ∧ t ≤ P ∧ (m + 2 : ℕ) * t ≤ P ∧
      allocatedSiteErrorFourierOutput m u (siteSourceMaskLog m q) (allocatedIdealProfileLog m u e) ≤ P := by
  have hq := (allocatedGeometricSourceBudget_controls m hp hc he hE).1
  have hu := (siteSourceParameter_bounds m hq).1
  have hw := siteSourceMaskLog_nonneg m hq
  have hv := allocatedIdealProfileLog_nonneg m hu he
  have hF := hu.trans (allocatedSiteErrorFourier_budgets m hu hw hv).2.2.2.2.1
  have hmt : t ≤ (m + 2 : ℕ) * t := by
    have hm := Nat.cast_nonneg (α := ℝ) m
    push_cast
    nlinarith
  dsimp only [allocatedGeometricSamplingInput]
  have hm := Nat.cast_nonneg (α := ℝ) (m + 2)
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · exact le_add_of_nonneg_left (mul_nonneg hm (by linarith))

theorem allocatedGeometricSamplingInput_dimension (m dim : ℕ) {p c e E t : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hdim : dim ≤ m + 1) (X : Type*) [Fintype X] (hX : (Fintype.card X : ℝ) ≤ t) :
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ allocatedGeometricSamplingInput m p c e E t := by
  have hd : (dim + 1 : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  calc
    _ = (dim + 1 : ℝ) * Fintype.card X := by simp [Fintype.card_prod, Fintype.card_option]
    _ ≤ (m + 2 : ℕ) * t := mul_le_mul hd hX (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ ≤ _ := (allocatedGeometricSamplingInput_controls m hp hc he hE ht).2.2.1

theorem map_allocatedGeometrySourceInput {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (m : ℕ) (p c e E : A) :
    f (allocatedGeometrySourceInput m p c e E) = allocatedGeometrySourceInput m (f p) (f c) (f e) (f E) := by
  simp [map_ofNat, allocatedGeometrySourceInput, allocatedGeometryInput,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedSiteScaleLog, allocatedSiteScaleNumeric, allocatedSiteKernelMaskLog,
    allocatedComparisonDimension, allocatedIdealScaleLog, allocatedIdealScaleInput,
    allocatedPhysicalIdealLengthEnvelope, allocatedTestLengthEnvelope, allocatedJointLengthEnvelope,
    allocatedTestEnvelope, allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
    allocatedKernelEnvelope, allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope,
    allocatedIdealRadiusEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
    allocatedSupportEnvelope, allocatedDensityEnvelope, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope]

theorem map_allocatedSiteErrorFourierOutput {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (m : ℕ) (p w v : A) :
    f (allocatedSiteErrorFourierOutput m p w v) = allocatedSiteErrorFourierOutput m (f p) (f w) (f v) := by
  simp [map_ofNat, allocatedSiteErrorFourierOutput, allocatedSiteErrorFourierInput,
    allocatedSiteErrorPrimitiveLog, allocatedErrorPrimitiveLog, allocatedErrorKernelLog,
    allocatedComparisonDimension]

theorem map_allocatedGeometricSamplingInput {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (m : ℕ) (p c e E t : A) :
    f (allocatedGeometricSamplingInput m p c e E t) =
      allocatedGeometricSamplingInput m (f p) (f c) (f e) (f E) (f t) := by
  simp [map_ofNat, allocatedGeometricSamplingInput, map_allocatedSiteErrorFourierOutput,
    siteSourceParameter, siteSourceMaskLog, canonicalScalarSourceLog, allocatedIdealProfileLog,
    allocatedComparisonDimension, map_allocatedGeometrySourceInput]

noncomputable def allocatedGeometricSamplingThreshold {A : Type*} [Semiring A]
    (m K : ℕ) (p c e E t : A) : A :=
  (allocatedGeometricSamplingInput m p c e E t + K) ^ K

theorem exists_allocatedGeometricSamplingThreshold_bound (m K : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedGeometricSamplingThreshold m K p p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedGeometricSamplingThreshold m K
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  have heval : poly.eval₂ (Nat.castRingHom ℝ) p = allocatedGeometricSamplingThreshold m K p p p p p := by
    simp only [poly, allocatedGeometricSamplingThreshold, Polynomial.eval₂_pow, Polynomial.eval₂_add,
      Polynomial.eval₂_natCast]
    have h := map_allocatedGeometricSamplingInput (Polynomial.eval₂RingHom (Nat.castRingHom ℝ) p)
      m Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
    simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using congrArg (fun x : ℝ => (x + K) ^ K) h
  exact heval ▸ hbound p hp

end Erdos3.VectorPolynomial

end

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

def AllocatedGeometricCoverAt (K : ℕ) : Prop :=
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
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (selection : Fin dim ↪ G) {κ : ℝ}
        (_hx : GoodScalarKernelTuple selection κ M₀ x),
      ∃ t : Fin M₀,
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period t : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (rowTypes j) (period t : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
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
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ (period t) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period t))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period t) (witnesses t) hb o bW d (g t) τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E)

theorem allocatedGeometricCoverAt_of_sampling {K : ℕ}
    (hSampling : ∀ inst : ∀ j : Fin m,
      Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)},
      @AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K
        (fun j => {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)})
        inst (fun _ => Subtype.val)) :
    AllocatedGeometricCoverAt.{uG,uI,uB,uJ,uQ,uX} (dim := dim) (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ)
      (S := S) (M₀ := M₀) (p := p) (c := c) (e := e) (E := E) K := by
  intro hp hc he hE hdimSmall hvars hI hn₁ hJ hcutoff hScale hσi hRadius
    hforward hinverse hvolume hσ1 hBlocks
  obtain ⟨witnesses, hBounds, hgeometry⟩ := geometric_good_kernel_ideal_cover_at_sampling
    (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (S := S) (M₀ := M₀)
    (hSampling := hSampling) hp hc he hE hdimSmall hvars hI hn₁ hJ hcutoff
    hScale hσi hRadius hforward hinverse hvolume hσ1 hBlocks
  refine ⟨witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _
  obtain ⟨g, hg, hcoeff, hmass, hcomparison⟩ := hgeometry hb o bW d
  refine ⟨g, hg, hcoeff, hmass, ?_⟩
  intro x selection κ hx
  obtain ⟨periodIndex, hspatial, hperiod, hcompare⟩ := hcomparison x selection hx
  refine ⟨periodIndex, hspatial, hperiod, ?_⟩
  intro τ hτ hτ1 hτe X _ _ Pbase hPbase hX _ _ _ μ _ _ ν _ _ polynomial hdegree hmp
    stride hstridePos R₁ S₀ ρ hS₀ hSP hρ hρP hstride H hH hrank hRlarge cells hcells W hW hwidth
  have hbudget := allocatedGeometricSamplingInput_controls m hp hc he hE hPbase
  have hdimBudget := allocatedGeometricSamplingInput_dimension m dim hp hc he hE hPbase hdimSmall X hX
  have hexp := Real.exp_le_exp.mpr hbudget.2.1
  exact hcompare τ hτ hτ1 hτe (X := X) (P₀ := samplingInput Pbase)
    hbudget.1 (hX.trans hbudget.2.1) hdimBudget hbudget.2.2.2
    μ ν polynomial hdegree hmp stride hstridePos hS₀ (hSP.trans hexp) hρ (hρP.trans hexp)
    hstride H hH hrank hRlarge cells hcells W hW hwidth

theorem exists_uniform_geometric_cover (m dim : ℕ) :
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
      AllocatedGeometricCoverAt.{uG,uI,uB,uJ,uQ,uX} (dim := dim) (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ)
        (S := S) (M₀ := M₀) (p := p) (c := c) (e := e) (E := E) K := by
  obtain ⟨K, hK, hSampling⟩ := exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨a, ha, hbound⟩ := exists_allocatedGeometricSamplingThreshold_bound m K
  refine ⟨K, a, hK, ha, hbound, ?_⟩
  intro G _ I _ _ n B _ _ J _ U b p c e E R σ hR hσ S M₀
  exact allocatedGeometricCoverAt_of_sampling (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ)
    (S := S) (M₀ := M₀) (p := p) (c := c) (e := e) (E := E) hSampling

end Erdos3.VectorPolynomial

end

end OAI
