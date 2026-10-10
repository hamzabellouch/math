import OAI.Combinatorics.Progressions.Dynamics.AllocatedCanonicalBudget
import OAI.Combinatorics.Progressions.Linear.AllocatedSupportedSlicedGoodKernelSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

private theorem accurateOneCubeAllRows (m : ℕ) :
    ∀ (j : Fin m) (t : Finset (Fin 1)), t ∈ boundedBooleanJetRows (Fin 1) (j.val + 1) := by
  intro j t
  rw [boundedBooleanJetRows_oneCube (j.val + 1) (by omega)]
  exact Finset.mem_univ t

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin 1) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j : Fin m, ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedSlicedRowIdeal B U b S rowSets hR (accurateOneCubeAllRows m) hB lower width

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

include hR hC hchart hbudget in
theorem exists_allocated_supported_sliced_accurate_source
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Qgrid)
    (hq : 0 < q) {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin 1) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin 1) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (rowSets j).card
      ((j.val + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin 1) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (h4 : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    {Pcap : ℝ} (hPcap : 0 ≤ Pcap) (haPcap : a⁻¹ ≤ Real.exp Pcap) (hδPcap : δ⁻¹ ≤ Real.exp Pcap)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    {Pnum Pk target : ℝ} (hPnum : 0 ≤ Pnum) (hPk : 0 ≤ Pk) (htarget : 0 ≤ target)
    {Mk : ℕ} (hMk : 0 < Mk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum) :
    let F := (m * (2 : ℝ) ^ Fintype.card (Fin 1)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * ((m + 1 : ℕ) * Pk))
    let Eg := slicedJointDensityLogBudget O m Pcap + (target + F) + 1
    let _εgrid := Real.exp (-Eg)
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ((j.val + 1) * (rowSets j).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin 1))) (L j Eg') + (Dg + 1) * (vg + 1))
    let Glog := Dg * max Op 0
    let ε := Real.exp (-(Glog + (target + F) + 1))
    let P := max Pcap (Glog + (target + F) + 2)
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin 1)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin 1) S.value)
        (selection : Fin 1 ↪ G)
        (_hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x),
      ∃ candidate : Fin Mk,
        let period := kernelPeriodCandidate (m + 1) candidate
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin 1) (period : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        ∀ (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
          (d : ℕ) [NeZero d] (_hdiv : period ∣ d) (_hqperiod : period ∣ q)
        (_hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
          (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
        (_hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))),
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    let Q := slicedJointDensityLogBudget O m P + P
    let A := Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, (4 : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin 1)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedSlicedRowIdeal B U b S rowSets hR (accurateOneCubeAllRows m) hB lower width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            Real.exp (-target)) ∧
        (∀ (μ : Measure (EuclideanJetLayers U rowTypes)) [IsProbabilityMeasure μ]
          (φ : EuclideanJetLayers U rowTypes → ℂ), Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
          ‖(∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) * φ y ∂μ) -
            ∫ y, (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y) * φ y ∂μ‖ ≤ Real.exp (-target)) ∧
        ∀ {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
          (hm : ∀ j e, coefficients (poly j) e ∈ U j),
          let Lcoord : ℝ≥0 := K * ∑ j, Cforward j * Fintype.card (J j)
          let Llong : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
            max ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) * Lcoord * (Mk ^ (m + 1) : ℝ≥0)) (4 * (Mk ^ (m + 1) : ℝ≥0))
          let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
          let Dcap : ℝ≥0 := ⟨Dg, hDg⟩
          let Lperiod : ℝ≥0 := ⟨Real.exp (Dg * max Op 0), Real.exp_nonneg _⟩
          let Lgrid : ℝ≥0 := max (((Dcap * Lprimitive) * Qgrid) *
            Lcoord * Lperiod) (4 * Lperiod)
          ∃ g : (Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
              (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin 1) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith (Llong + Lgrid) (g label i kg t)) ∧
            (∀ label i kg t z, ‖g label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g := by
  intro F Eg εgrid p L Cp E' Op Glog ε P
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hEg : 0 ≤ Eg := by
    have hcap := slicedJointDensityLogBudget_nonneg O m hPcap
    dsimp only [Eg]
    linarith
  obtain ⟨hg0, _, hgi, hl0, _, hli, hP, haP, hδP, hfour, _⟩ :=
    slicedSourceErrorBudget_of_card_le (ι := gridAxes) O m (Op := Op) hDg haxes hPcap htarget hF
      (C := 0) (by norm_num) (Real.exp_nonneg F) haPcap hδPcap
  obtain ⟨e, heb, he⟩ := exists_allocated_supported_sliced_good_kernel_source
    B U b S q r hr hb o bW hR C hC hchart hbudget hB lower width hσ H step c hH hsubset label hcell
    Cforward hforward K hK Qgrid hQgrid hq hδg hdenseg Tg hQTg hstep Ag hAg Pg hPg hcP hsP
    hstride hBa hBi hDg hvg hwg htg hpg hEg hcube hdegree hrowsD htail hblocks hRv hRi hδw hTg
    hcoeff hPp₀ haxes hg0 hgi.le hσgrid T hT h4 hsource hradius hσ1 O hO hwidth ha hδ hP
    haP hδP hPcap haPcap hδPcap hprincipal hw hl hl0 hfour hli
  refine ⟨e, heb, ?_⟩
  intro x selection hx
  obtain ⟨candidate, hspatial, hsourceModel⟩ := he x hMk selection hx
  refine ⟨candidate, hspatial, ?_⟩
  intro y₀ d hd hdiv hqperiod hu₀ hy₀
  let period := kernelPeriodCandidate (m + 1) candidate
  obtain ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr, hphysical⟩ :=
    hsourceModel y₀ d hdiv hqperiod hu₀ hy₀
  have hpref := allocatedSlicedSourceEarlyPrefactor_le_exp B U b S rowSets E hR
    hPnum hI hn hcoeffEarly hRiEarly hVEarly hMkPk
    (kernelPeriodCandidate_le_exp hMkPk (m + 1) candidate)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, herror⟩ :=
    slicedSourceErrorBudget_of_card_le (ι := gridAxes) O m (Op := Op) hDg haxes hPcap htarget hF
      (mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (coefficientDeckPeriodCap_nonneg rowTypes E period))) hpref haPcap hδPcap
  have herrSmall := fun y => (herr y).trans herror
  refine ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herrSmall, ?_, ?_⟩
  · intro μ hμ φ hφ hφb
    have hsm := allocatedWholeMaskedSlicedProfile_mean_measurable B U b hR hσ S rowSets
      (accurateOneCubeAllRows m) x hb o bW d hB lower width gridLaw
      (fun u => principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q
    exact (allocatedFiniteSourceModel_test_error B U b S rowSets x y₀ q d period r hr hb o bW
      μ a₀ f hLf hf e heb _ hsm herrSmall φ hφ hφb).2

  · intro X poly hp hm Lcoord Llong Lprimitive Dcap Lperiod Lgrid
    obtain ⟨g, hg, hgb, hidentity⟩ := hphysical poly hp hm
    refine ⟨g, ?_, hgb, hidentity⟩
    have hcardg : (Fintype.card gridAxes : ℝ≥0) ≤ Dcap := by exact_mod_cast haxes
    have hperiodg : Lprimitive ^ Fintype.card gridAxes ≤ Lperiod := by
      have hreal : (Real.exp Op) ^ Fintype.card gridAxes ≤ Real.exp (Dg * max Op 0) := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right haxes (le_max_right _ _))
      exact_mod_cast hreal
    intro label i kg site
    apply (hg label i kg site).weaken
    apply add_le_add le_rfl
    apply max_le_max
    · apply mul_le_mul _ hperiodg zero_le zero_le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcardg zero_le) zero_le) zero_le
    · exact mul_le_mul_of_nonneg_left hperiodg zero_le

end Erdos3.VectorPolynomial

end

end OAI
