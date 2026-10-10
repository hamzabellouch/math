import OAI.Combinatorics.Progressions.Geometry.FixedSpatialNativeAmbientComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val] (Aexp : ℕ → ℕ)
local notation "primes" => (fun p : Pr => Subtype.val p)
local notation "exponent" => (fun p : Pr => Aexp (Subtype.val p))
local notation "N" => (∏ p : Pr, Subtype.val p ^ Aexp (Subtype.val p))
local instance fixedPathRecoveredAmbientCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

local instance fixedPathRecoveredAmbientCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

variable [hLattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hR hσ ν hLattice hcompact in
theorem allocatedFixedPath_recovered_native_ambient_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ)
    (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
    (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
    (hbase : canonicalCoefficientSample U basis hb o sample =
      affineSampleCoefficientTorus U nativePoly hmem
        (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
          integerFrame) (k, x) : ℝ)))
    (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
      coefficientDeckChartEvent U bW basis hb o W.cover event
        (affineCoefficientCoverSample U nativePoly hmem W.cover
          (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
            integerFrame) (k, x) : ℝ))) ↔
        event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))
    (hnoise : allocatedReadNoise read = integerFrame)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d)
    {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernelRank : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis short j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (Dmod : ℕ)
    (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ Dmod)
    (hp : ∀ p ∈ Pr, p.Prime) (Rbad : ℕ)
    (hbad : (∏ p ∈ Pr, p ^ largestTestedBadDepth Aexp
      (allocatedActualPrimeBad short spatial kernelRank block Pr
        (modularForecastRankConstant m Dmod : ℝ)) p read) ≤ Rbad)
    (origin : ∀ p : Pr, Long → ZMod (p.val ^ Aexp p.val))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (d : ℕ) {Pbound Eerr Q Pτ PR : ℝ} (hPbound : 0 ≤ Pbound) (hEerr : 0 ≤ Eerr)
    (hDP : (Rbad : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
        modularRankChargeFactor m) ≤ Real.exp Pbound)
    (hdOut : Fintype.card Out ≤ d)
    (hdJoint : Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value) ≤ d)
    (hdCont : Fintype.card (Σ j : Fin m, I j) ≤ d)
    (hqexp : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hfloor : forecastJointGridSamplerFloor d Pbound Eerr Q PR ≤ S.value)
    (hboxLarge : ∀ i, Real.exp (forecastJointGridAmbientLog d Pbound Eerr Q Pτ) ≤ (box i : ℝ))
    (hcap : (fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ)
        (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true h1)
      (δ := 1 / 2) (by norm_num) : ℝ) ≤ Real.exp Pbound)
    (hLip : (fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ)
        (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false h0)
      (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ)
        (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true h1)
      (δ := 1 / 2) (by norm_num) : ℝ) ≤ Real.exp Pbound)
    (htestLip : ((Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R) : ℝ≥0) : ℝ) ≤
      Real.exp Pbound)
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (radius : ℝ≥0) (hradiusPos : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
    (hmonomials : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
    (hchartNorm : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      chartCap j * ‖v‖)
    (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
    (hbaseBox : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
    (hVpos : 0 < gridVolume) :
    let projection := allocatedOriginalSampleCongruenceProjection B U basis S sample
    let poly := allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) h0 h1 hB lower width sample
    let pRat := crtPolynomialInputLaw primes exponent (fun _ : Pr => 0)
      (primePower_crt_coprime primes exponent (fun p => hp p.val p.property)
        Subtype.val_injective) origin
    let Y := fun v : Original => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N
    let κ := ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ)
    ∀ {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
      (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
      (coeff : Findex → ℂ) (δforecast : ℝ),
    (∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hmem' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
      ‖κ * forecastDensityPhysicalTarget B U basis S density selected sample xref
        (fun _ => pRat) Y N gridVolume base box τ o hb bW poly' hmem' u -
        ∑ i, coeff i * (F i).eval box poly' u‖ ≤ δforecast) →
    ∀ {Pambient Eambient Rrank M : ℝ}, 0 ≤ Pambient → 0 ≤ Eambient →
    (Fintype.card X : ℝ) ≤ Pambient → (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient →
    ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤
      Real.exp Pambient →
    (∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient) →
    (∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient) →
    (∑ i, ‖coeff i‖) ≤ M →
    (∀ i, Real.exp ((max Pambient Eambient + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (box i : ℝ)) →
    Real.exp ((max Pambient Eambient + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ)) Rrank (U j) (nativePoly j)) →
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        W.eval box nativePoly (fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))) -
      (𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * forecastDensityPhysicalTarget B U basis S density selected sample xref
          (fun _ => pRat) Y N gridVolume base box τ o hb bW nativePoly hmem u))‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) + (Kφ : ℝ) * ξ + Real.exp (-Eerr) + (2 * δforecast + M * Real.exp (-Eambient)) := by
  classical
  intro projection poly lower width Kφ K kernel law density pRat Y κ
    Findex instF pf cf Lf F coeff δforecast happrox Pambient Eambient Rrank M
    hPa hEa hXa hJa hLa hCa hMa hmass hlarge hRrank hrank
  let c := fun a => (sample (selected a).1).2 (selected a).2
  let grid := forecastInactiveFixedOutput B U basis S selected c xref
  let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  have hsource := allocatedFixedPath_recovered_native_jointGrid_comparison
    B U basis hR hσ S Pr Aexp hb o bW W τ ξ hτ hξ box hbox integerFrame hframe
    e h0 h1 hB sample hs ht hσbound b hη A hA htail hS q hsize hsmall hm hperiod hcover
    xref base nativePoly hmem hdegree hbase hsmallChart read hread hnoise hinteger
    spatial kernelRank block Dmod hDmod hp Rbad hbad origin hqN hV
    d hPbound hEerr hDP hdOut hdJoint hdCont hqexp hτinv hRinv hfloor hboxLarge
    hcap hLip htestLip
  have hg := allocatedFixedPathKernelFrame_geometry B U basis S hτ hξ box hbox integerFrame hframe
  have hambient := fixedSpatialNativeAmbientMean_comparison
    B U basis hR hσ S sample xref (fun _ => pRat) Y N gridVolume base box τ o hb bW W ν
    e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame)
    h0 h1 hB hs hS hσ1 radius hradiusPos hradius3 hmonomials chartCap hchartCap hchartNorm
    hchartBudget hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 hτ hmargin hbaseBox q hqN hm hperiod hcover hVpos
    F coeff δforecast happrox nativePoly hdegree hmem hPa hEa hXa hJa hLa hCa hMa hmass
    hlarge hRrank hrank
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (kernel.complexMean (fun x => law.complexMean (fun v =>
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))))
    (forecastJointOriginalGridMean U basis S.value hm law (fun _ => pRat) grid Y N q hqN
      gridVolume density test (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
      (forecastJointGridScale U basis R S.value box τ))
    (𝔼 u ∈ integerBox box, W.eval box nativePoly u *
      (κ * forecastDensityPhysicalTarget B U basis S density selected sample xref
        (fun _ => pRat) Y N gridVolume base box τ o hb bW nativePoly hmem u))
  exact htriangle.trans (add_le_add hsource ((norm_sub_rev _ _).trans_le hambient))

end Erdos3.VectorPolynomial

end

end OAI
