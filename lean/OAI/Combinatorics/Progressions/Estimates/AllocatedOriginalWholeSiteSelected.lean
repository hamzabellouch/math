import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalAmbientSelected
import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedBufferedPhysicalFactorization

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedOriginalUnitSiteSelectedAt (D Psp E e t : ℝ) (A T Kproj Kideal Kbuf : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 1 + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    (_hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (Kscale : ℝ≥0) (_hKscale : ∀ j, (R j)⁻¹ ≤ Kscale)
    {pNum : ℝ} (_hPspNum : Psp ≤ pNum)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp pNum)
    (_herrorNum : profileReferenceErrorLog Psp (E + 1 + 4) ≤ pNum)
    (_hRefineNum : (m + 1 : ℕ) * Psp + Psp ^ 2 + (dim + 1 : ℕ) ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum),
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Fbuf := allocatedProfileFourierOutput
    (allocatedSiteBufferInput m D pNum (allocatedSiteEnvelopeGain m D Psp) lengthLog (normalizedSiteCutoffBound : ℝ))
  let Q := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l (F + Fbuf)
  let K := max Kbuf (max T (max Kproj Kideal))
  let pSite := allocatedSiteApproximationInput m dim D Psp E e
  let Qsite := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card (Fin dim)) pSite
  let radius : ℝ≥0 := ⟨idealSiteBoxRadius (Fin dim) m, (idealSiteBoxRadius_pos (Fin dim) m).le⟩
  let Ccut : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Qsite + 8) ∧
    (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8)) ∧
    ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
      (g : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) →
        (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ),
      (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8) + Qsite + Fintype.card (Finset (Fin dim))) ∧
      (∀ i s v, ‖g i s v‖ ≤ 1) ∧
      (∀ i s, LipschitzWith ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Qsite + 12), Real.exp_nonneg _⟩ + Ccut) *
        (Kscale * ∑ j, C j * Fintype.card (J j))) (g i s)) ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ Mk ^ (m + 1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range) ∧
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
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (V : Fin m → ℝ≥0)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedBufferedPhysicalChartRadius (G := G) B (Fin dim) Cinv j)
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 1 + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 1 + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 1 + 2) W / 4
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
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
      ∑ i, a i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hMk selection hx modulus q reference N hW mesh base cells
        (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z
        (fun u r y => (allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
          jetRows hb o bW d (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedMaskedSiteEnvelope B U b S x modulus (residue u r)) y : ℂ) *
          ∏ site, g i site (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y site)))‖ ≤
      Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem allocatedOriginalSiteSelectedAt_unit
    {D Psp E e t : ℝ} {A T Kproj Kideal Kbuf : ℕ} (ht1 : t ≤ 1)
    (hselected : AllocatedOriginalSiteSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf) :
    AllocatedOriginalUnitSiteSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf := by
  unfold AllocatedOriginalUnitSiteSelectedAt
  intro w error gainLog hmPsp hdimPsp hGPsp hvarsGrowth J _ U b R σ hR hσ hσt o C hC Kscale hKscale
    pNum hPspNum hcount herrorNum hRefineNum hRP hRi hσi S lengthLog Pbase l F Fbuf Q K
    pSite Qsite radius Ccut
  obtain ⟨hS, k, hk, hcard, a, f, ha, hf, hLf, hsupport, hselected⟩ :=
    hselected hmPsp hdimPsp hGPsp hvarsGrowth U b hR hσ hσt
      hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  obtain ⟨g, hLg, hg, hvalue⟩ :=
    exists_allocated_unit_site_family B U b hR S o f C hC Kscale hKscale _ hLf hf
  refine ⟨hS, k, hk, hcard, (fun i => a i * (2 : ℂ) ^ Fintype.card (Finset (Fin dim))),
    g, unitSiteCoefficientMass_le_exp a _ ha, hg, hLg, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, modulus, hmodulus, hselected⟩ := hselected x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmodulusSize, hspatialPeriod, hcoefficientPeriod, s, hA, hinverse, hselected⟩ := hselected
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatialPeriod, hcoefficientPeriod,
    s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb Kcov _ bW V hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  have hsmallOriginal (j) : R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j :=
    (hsmall j).trans (allocatedBufferedPhysicalChartRadius_le_original B (Fin dim) Cinv hCinv j)
  have hsmallSupported (j) : R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv
      (allocatedSiteRootAllowance (Fin dim) m) j :=
    (hsmall j).trans (allocatedBufferedPhysicalChartRadius_le_supported B (Fin dim) Cinv j)
  have hσ1 (j) : σ j ≤ 1 := (hσt j).trans ht1
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hselected⟩ :=
    hselected block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmallOriginal μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  obtain ⟨hmass, horiginal⟩ := hselected hτ hτP N hN hsizeN poly hpoly hmem hrank hRank
    base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hrew (i) := allocatedRefinedUnitSiteReference_eq (τ := τ) (ξ := ξ)
    B U b hR hσ S x X hMk selection hx modulus q reference residue hb o bW d N hW mesh base cells
    (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z hσ1 Cinv hCinv hchart
    hsmallSupported (f i) (hsupport i) (g i) (hvalue i)
  refine le_trans (le_of_eq ?_) horiginal
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [hrew]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_original_unit_site_selected
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) :
    ∃ K : ℕ, 2 ≤ K ∧
      let target := profileReferenceErrorLog Psp (E + 1 + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) hLayer A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            ∃ Kbuf : ℕ, 2 ≤ Kbuf ∧
              AllocatedOriginalUnitSiteSelectedAt.{_, _, _, uGeom, uCover, uSpace}
                (G := G) (dim := dim) B D Psp E e t A₀ T₀ Kproj K Kbuf := by
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
      Kbuf, hKbuf, hselected⟩ :=
    exists_allocated_original_site_selected.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    Kbuf, hKbuf, allocatedOriginalSiteSelectedAt_unit B ht1 hselected⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedOriginalWholeSiteAt (D Psp E e t : ℝ) (A T Kproj Kideal Kbuf : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 1 + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    (_hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (Kscale : ℝ≥0) (_hKscale : ∀ j, (R j)⁻¹ ≤ Kscale)
    {pNum : ℝ} (_hPspNum : Psp ≤ pNum)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp pNum)
    (_herrorNum : profileReferenceErrorLog Psp (E + 1 + 4) ≤ pNum)
    (_hRefineNum : (m + 1 : ℕ) * Psp + Psp ^ 2 + (dim + 1 : ℕ) ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum),
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Fbuf := allocatedProfileFourierOutput
    (allocatedSiteBufferInput m D pNum (allocatedSiteEnvelopeGain m D Psp) lengthLog (normalizedSiteCutoffBound : ℝ))
  let Q := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l (F + Fbuf)
  let K := max Kbuf (max T (max Kproj Kideal))
  let pSite := allocatedSiteApproximationInput m dim D Psp E e
  let Qsite := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card (Fin dim)) pSite
  let radius : ℝ≥0 := ⟨idealSiteBoxRadius (Fin dim) m, (idealSiteBoxRadius_pos (Fin dim) m).le⟩
  let Ccut : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Qsite + 8) ∧
    (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8)) ∧
    ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
      (g : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) →
        (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ),
      (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8) + Qsite + Fintype.card (Finset (Fin dim))) ∧
      (∀ i s v, ‖g i s v‖ ≤ 1) ∧
      (∀ i s, LipschitzWith ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Qsite + 12), Real.exp_nonneg _⟩ + Ccut) *
        (Kscale * ∑ j, C j * Fintype.card (J j))) (g i s)) ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ Mk ^ (m + 1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range) ∧
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
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (V : Fin m → ℝ≥0)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedBufferedPhysicalChartRadius (G := G) B (Fin dim) Cinv j)
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 1 + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 1 + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 1 + 2) W / 4
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
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
      ∑ i, a i * ((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).complexMean
        (allocatedWholeProfileReferenceTerm (τ := τ) (ξ := ξ)
          B U b S x X hMk selection hx modulus q reference N hW mesh base cells
          (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test)
          (fun y z => (allocatedWholeResidueProfile B U b hR hσ S x jetRows modulus hb o bW d
            (allocatedMaskedSiteEnvelope B U b S x modulus) y z : ℂ) *
            ∏ site, g i site (coveredJetAmbientTorus U d (coveredBooleanSiteValue U z site)))) /
          (Z : ℂ))‖ ≤
      Real.exp (-E)

theorem allocatedOriginalUnitSiteSelectedAt_whole
    {D Psp E e t : ℝ} {A T Kproj Kideal Kbuf : ℕ}
    (hselected : AllocatedOriginalUnitSiteSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf) :
    AllocatedOriginalWholeSiteAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf := by
  unfold AllocatedOriginalWholeSiteAt
  intro w error gainLog hmPsp hdimPsp hGPsp hvarsGrowth J _ U b R σ hR hσ hσt o C hC Kscale hKscale
    pNum hPspNum hcount herrorNum hRefineNum hRP hRi hσi S lengthLog Pbase l F Fbuf Q K
    pSite Qsite radius Ccut
  obtain ⟨hS, k, hk, hcard, a, g, ha, hg, hLg, hselected⟩ :=
    hselected hmPsp hdimPsp hGPsp hvarsGrowth U b hR hσ hσt o C hC Kscale hKscale
      hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  refine ⟨hS, k, hk, hcard, a, g, ha, hg, hLg, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, modulus, hmodulus, hselected⟩ := hselected x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmodulusSize, hspatialPeriod, hcoefficientPeriod, s, hA, hinverse, hselected⟩ := hselected
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatialPeriod, hcoefficientPeriod,
    s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb Kcov _ bW V hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hselected⟩ :=
    hselected block hb bW V hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  obtain ⟨hmass, horiginal⟩ := hselected hτ hτP N hN hsizeN poly hpoly hmem hrank hRank
    base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hrew (i) := allocatedRefinedFamilyReference_whole (τ := τ) (ξ := ξ)
    B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d N hW mesh
    base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z
    hcoefficientPeriod hRefined hsize href hresidue (allocatedMaskedSiteEnvelope B U b S x modulus)
    (fun z => ∏ site, g i site (coveredJetAmbientTorus U d (coveredBooleanSiteValue U z site)))
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun i _ => congrArg (fun z : ℂ => a i * z) (hrew i))
  rw [hsum] at horiginal
  exact horiginal

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_original_whole_site_selected
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) :
    ∃ K : ℕ, 2 ≤ K ∧
      let target := profileReferenceErrorLog Psp (E + 1 + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) hLayer A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            ∃ Kbuf : ℕ, 2 ≤ Kbuf ∧
              AllocatedOriginalWholeSiteAt.{_, _, _, uGeom, uCover, uSpace}
                (G := G) (dim := dim) B D Psp E e t A₀ T₀ Kproj K Kbuf := by
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
      Kbuf, hKbuf, hselected⟩ :=
    exists_allocated_original_unit_site_selected.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    Kbuf, hKbuf, allocatedOriginalUnitSiteSelectedAt_whole B hselected⟩

end Erdos3.VectorPolynomial

end

end OAI
