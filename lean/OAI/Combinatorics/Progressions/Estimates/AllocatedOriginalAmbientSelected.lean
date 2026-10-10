import OAI.Combinatorics.Progressions.Dynamics.AmbientSiteExpansionBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalAmbientSelectedAt
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSelected

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

def AllocatedOriginalSiteSelectedAt (D Psp E e t : ℝ) (A T Kproj Kideal Kbuf : ℕ) : Prop :=
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
      (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
      (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8) + Qsite) ∧
      (∀ i s v, ‖f i s v‖ ≤ 1) ∧
      (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Qsite + 12), Real.exp_nonneg _⟩ + Ccut) (f i s)) ∧
      (∀ i s v, (∃ d, 2 * idealSiteBoxRadius (Fin dim) m < |v d|) → f i s v = 0) ∧
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
        (fun u r => allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r)
          jetRows hb o bW d (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedSiteTermDensity B U b S x modulus (residue u r) (f i)))‖ ≤
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

theorem allocatedOriginalSiteSelectedAt_ambient
    {D Psp E e t : ℝ} {A T Kproj Kideal Kbuf : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D) (ht1 : t ≤ 1)
    (hselected : AllocatedOriginalSiteSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf) :
    AllocatedOriginalAmbientSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf := by
  unfold AllocatedOriginalAmbientSelectedAt
  intro w error gainLog hmPsp hdimPsp hGPsp hvarsGrowth J _ U b R σ hR hσ hσt
    pNum hPspNum hDNum herrorNum hRefineNum hRP hRi hσi o C hC hCp
    S lengthLog Pbase l F Fbuf Q K pSite Qsite radius Ccut
  have hcount (j : Fin m) : (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤
      Real.exp pNum :=
    (add_le_add ((hdim.coefficients j).trans hDNum) (le_refl (1 : ℝ))).trans
      (Real.add_one_le_exp pNum)
  obtain ⟨hS, k, hk, hcard, a, f, ha, hf, hLf, hsupport, hselected⟩ :=
    hselected hmPsp hdimPsp hGPsp hvarsGrowth U b hR hσ hσt
      hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  let Kinv : ℝ≥0 := ⟨Real.exp pNum, Real.exp_nonneg _⟩
  let Lsite : ℝ≥0 :=
    ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Qsite + 12), Real.exp_nonneg _⟩ + Ccut
  have hJ (j) : (Fintype.card (J j) : ℝ) ≤ pNum :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans (hdim.axes.trans hDNum)
  have hweight : Kinv * (∑ j, C j * Fintype.card (J j)) ≤
      (⟨Real.exp (4 * pNum), Real.exp_nonneg _⟩ : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    change Real.exp pNum * ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp (4 * pNum)
    simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast] using
      ambient_site_lipschitz_weight_bound C (hdim.degree.trans hDNum) hJ hCp
  choose g hLg hgnorm hgvalue using fun i s =>
    exists_allocated_unit_ambient_site_factor B U b S o hR C hC Kinv hRi
      (f i s) Lsite (hLf i s) (hf i s)
  refine ⟨hS, k, hk, hcard, (fun i => a i * (2 : ℂ) ^ Fintype.card (Finset (Fin dim))),
    g, complex_coefficient_two_power_mass a _ ha, hgnorm, ?_, ?_⟩
  · intro i s
    exact (hLg i s).weaken (mul_le_mul_of_nonneg_left hweight zero_le)
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, modulus, hmodulus, hselected⟩ := hselected x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmodulusSize, hspatialPeriod, hcoefficientPeriod, s, hA, hinverse, hselected⟩ := hselected
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatialPeriod, hcoefficientPeriod,
    s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb Kcov _ bW V hV hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  have hsmallOld (j) : R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j :=
    (hsmall j).trans (allocatedSiteChartRadius_le_original B (Fin dim) Cinv hCinv j)
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hselected⟩ :=
    hselected block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmallOld μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  obtain ⟨hmass, horiginal⟩ := hselected hτ hτP N hN hsizeN poly hpoly hmem hrank hRank
    base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hprofile :
      (fun u r y => ∑ i, a i *
        allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r)
          jetRows hb o bW d (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedSiteTermDensity B U b S x modulus (residue u r) (f i)) y) =
      (fun u r y => ∑ i, (a i * (2 : ℂ) ^ Fintype.card (Finset (Fin dim))) *
        ((allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
          jetRows hb o bW d (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedMaskedSiteEnvelope B U b S x modulus (residue u r)) y : ℂ) *
          ∏ s, g i s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)))) := by
    funext u r y
    apply Finset.sum_congr rfl
    intro i _
    rw [allocatedCoveredSiteTerm_unit_factorization B U b hR hσ S x u (reference u r)
      hb o bW d (fun j => (hσt j).trans ht1) Cinv hCinv hchart hsmall modulus
      (residue u r) (f i) (hsupport i) (g i) (hgvalue i) y]
    ring
  have heq := congrArg (fun profile => allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
    B U b S x X hMk selection hx modulus q reference N hW mesh base cells
      (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z profile) hprofile
  rw [allocatedRefinedComplexReference_sum, allocatedRefinedComplexReference_sum] at heq
  rw [← heq]
  exact horiginal

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

theorem allocatedOriginalSelectedAt_site
    {D Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (ht1 : t ≤ 1) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hselected : AllocatedOriginalSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp (E + 1) e t δ A T Kproj Kideal) :
    ∃ Kbuf : ℕ, 2 ≤ Kbuf ∧
      AllocatedOriginalSiteSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
        (G := G) (dim := dim) B D Psp E e t A T Kproj Kideal Kbuf := by
  obtain ⟨Kbuf, hKbuf, hbuffer⟩ :=
    exists_allocated_reference_buffer_mass.{uG, uI, uB, uGeom, uCover, uSpace} m dim
  refine ⟨Kbuf, hKbuf, ?_⟩
  unfold AllocatedOriginalSiteSelectedAt
  intro w error gainLog hmPsp hdimPsp hGPsp hvarsGrowth J _ U b R σ hR hσ hσt
    pNum hPspNum hcount herrorNum hRefineNum hRP hRi hσi S lengthLog Pbase l F Fbuf Q K
    pSite Qsite radius Ccut
  have hE1 : 0 ≤ E + 1 := by linarith
  have hpNum : 0 ≤ pNum := hPsp.trans hPspNum
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdim.nonneg hPsp (by linarith)
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have hlength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hdim.nonneg hpNum he hw herror
    exact h.2.1.trans h.2.2.2.2.2
  have hF : 0 ≤ F := allocatedProfileFourierOutput_nonneg
    (allocatedActualProfileInput_bounds m hdim.nonneg hpNum he hgain hlength).1
  have hFbuf : 0 ≤ Fbuf := allocatedProfileFourierOutput_nonneg
    (allocatedSiteBufferInput_bounds m hdim.nonneg hpNum
      (allocatedSiteEnvelopeGain_nonneg m hdim.nonneg hPsp) hlength normalizedSiteCutoffBound.coe_nonneg).1
  obtain ⟨_hPbase1, _hDPbase, hpBase, _hLBase, _hWBase⟩ :=
    allocatedIdealSourceBudget_bounds m hdim.nonneg hpNum he hw herror
  have hPspBase : Psp ≤ Pbase := hPspNum.trans hpBase
  obtain ⟨hS, hselected⟩ := hselected hmPsp hdimPsp hGPsp hvarsGrowth U b hR hσ hσt
    hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  obtain ⟨hpSite, heSite, herrorSite, hboxSite⟩ :=
    allocatedSiteApproximationInput_bounds m dim hdim.nonneg hPsp hE he
  let ε := siteReferenceAccuracy m D Psp (E + 1)
  have hε : 0 < ε := siteReferenceAccuracy_pos m D Psp (E + 1)
  have hεp : ε⁻¹ ≤ Real.exp pSite := by
    simpa only [ε, siteReferenceAccuracy, Real.exp_neg, inv_inv] using Real.exp_le_exp.mpr herrorSite
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, hsite⟩ :=
    exists_allocated_ideal_site_approximation (α := Fin dim) B U b S hR δ hδ hδ1 hε hpSite
      (by simpa only [Fintype.card_fin] using hboxSite)
      hεp (hδe.trans (Real.exp_le_exp.mpr heSite))
  refine ⟨hS, k, hk, hcard, a, f, ha, hf, hLf, hsupport, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, modulus, hmodulus, hselected⟩ := hselected x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmodulusSize, hspatialPeriod, hcoefficientPeriod, s, hA, hinverse, hselected⟩ := hselected
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatialPeriod, hcoefficientPeriod,
    s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  have hσ1 (j) : σ j ≤ 1 := (hσt j).trans ht1
  have hnum := allocatedIdealSource_numerics B U b o hdim hpNum he hw herror hR hσ hRi hσi C V hCp hVp
  have hJ (j) : (Fintype.card (J j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans hdim.axes
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hselected⟩ :=
    hselected block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  let C₀ : ℝ := 1 + (S.value : ℝ) + W
  let cap : ℝ := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
  let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
  let ρ := normalizedTupleResolution X indices selection Mk Psp (E + 1 + 2) C₀ W cap Centry
  have hcap : 0 ≤ cap := pow_nonneg (NNReal.coe_nonneg _) _
  obtain ⟨_hW, hl, hBaseL, hC₀, _hLC, _hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    AllocatedSourceNumerics.late_bounds B U b S C V hnum hR hσ
  have hWscale : W ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hql (a : X) : (q a : ℝ) ≤ Real.exp l :=
    (hqPsp a).trans (Real.exp_le_exp.mpr (hPspBase.trans hBaseL))
  have hτl : τ⁻¹ ≤ Real.exp l := by
    simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr (hpBase.trans hBaseL))
  have hE3 : 0 ≤ E + 1 + 2 := by linarith
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast Nat.succ_le_iff.mpr S.positive
  have hentry : 0 ≤ Centry := zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  obtain ⟨_hξ, hξ1, _hξlog, hchoices⟩ := normalizedTupleSpatialChoices
    (N := indices) (X := X) (m := m) selection hMk hPsp hE3 hmPsp hdimPsp hGPsp hXPsp hMkPsp
  obtain ⟨_hδ, _hδ1, hmesh, hρ, _hmeshSize, hρ8, hshift, _hmove, _hboundary, _hspatial⟩ :=
    hchoices (zero_le_one.trans hC₀) hW hS1 hcap hentry hvarsGrowth hWscale
  have hqdimBase : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using
      hdimPsp.trans hPspBase
  have hXBase : (Fintype.card X : ℝ) ≤ Pbase := hXPsp.trans hPspBase
  obtain ⟨hQ1, hBaseQ, _hE1Q, _hlQ, hFsQ, _hJetQ, hProdQ, _hWidthQ, _hSideQ⟩ :=
    allocatedSourceSamplingBudget_bounds m dim A hnum.nonneg hE1 hl (add_nonneg hF hFbuf)
  have hQ : 0 ≤ Q := zero_le_one.trans hQ1
  have hFbufQ : Fbuf ≤ Q := (le_add_of_nonneg_left hF).trans hFsQ
  obtain ⟨_hwidthQ, hsideQ, _hdimQ⟩ := allocatedSourceSamplingBudget_spatial m A X indices selection
    hPsp hE1 hl (add_nonneg hF hFbuf) hPspBase hqdimBase hnum.variable_count hXBase
  have hXQ := hXBase.trans hBaseQ
  have hOptionBase : (Fintype.card (Option (Fin dim)) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_option, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit, Nat.add_comm 1]
      using hqdimBase
  have hsmallDim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Q := by
    calc
      _ = (Fintype.card (Option (Fin dim)) : ℝ) * Fintype.card X := by
        simp only [Fintype.card_prod, Nat.cast_mul]
      _ ≤ Pbase * Pbase := mul_le_mul hOptionBase hXBase (Nat.cast_nonneg _) hnum.nonneg
      _ ≤ (Pbase + 1) * Pbase := mul_le_mul_of_nonneg_right (by linarith) hnum.nonneg
      _ ≤ Q := hProdQ
  obtain ⟨hOldCut, hQcut, hBufCut⟩ := allocatedSourceSamplingBudget_site_cutoffs m dim A
    hnum.nonneg hE hl hF hFbuf T Kproj Kideal Kbuf (Nat.le_trans (by decide) hT)
      (Nat.le_trans (by decide) hKbuf)
  have hside (a : X) : Real.exp (normalizedTupleSideLog X indices selection Psp (E + 1 + 2) l) ≤ (N a : ℝ) :=
    (Real.exp_le_exp.mpr (hsideQ.trans hQcut)).trans (hsizeN a)
  have hphysical (a : X) : 8 * (1 + W) * (q a : ℝ) * ρ ≤ (ξ * τ) * (N a : ℝ) :=
    normalizedTupleSpatialSize X indices selection hPsp hE3 hl hMk hmPsp hdimPsp hGPsp hXPsp hMkPsp
      (zero_le_one.trans hC₀) hW hcap hentry hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _) (hql a)
      hτ hτl (hside a)
  have hshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hshift
  obtain ⟨hmass, horiginal⟩ := hselected hτ hτP N hN
    (fun a => (Real.exp_le_exp.mpr hOldCut).trans (hsizeN a)) poly hpoly hmem hrank
    ((Real.exp_le_exp.mpr hOldCut).trans hRank) base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have htest' := physicalCubeSiteTest_norm_le test htest
  have hmassBuffer := hbuffer B U b hR hσ S x hdim hpNum hPsp hlength hRi hS hσ1 hJ
    hMk selection hx hMkPsp hqDim hb o bW d C V hC hV hCp hVp ν modulus hcoefficientPeriod
    hmodulusSize (hspatialPeriod (fun a => (0 : ℤ) + (x a none : ℤ))) q hq reference residue
    N hN hW hτ hξ hξ1 hρ hphysical hρ8 hshift' le_rfl base cells hmass poly hpoly hmem
    hQ hXQ hsmallDim (hτP.trans (Real.exp_le_exp.mpr (hpBase.trans hBaseQ)))
    (fun a => (hqPsp a).trans (Real.exp_le_exp.mpr (hPspBase.trans hBaseQ)))
    (fun a => (Real.exp_le_exp.mpr hBufCut).trans (hsizeN a)) hrank
    ((Real.exp_le_exp.mpr hBufCut).trans hRank) mesh hmesh hmPsp hdimPsp hGPsp hXPsp
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) hvarsGrowth hWscale hFbufQ
    (physicalCubeSiteTest test) htest'
  have hfinite := allocatedRefinedIdealReference_finite_site_error B U b hR hσ S x X hMk selection hx
    modulus q reference residue hb o bW d N hW mesh base cells (physicalCubeEuclideanSample U d poly hmem)
    (physicalCubeSiteTest test) Z a f δ hδ hδ1 hε.le le_rfl hZ hsupport (fun z => (hsite z).2) hmassBuffer
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ _ + _ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.exp (-(E + 1)) + Real.exp (-(E + 1)) := add_le_add horiginal hfinite
    _ = 2 * Real.exp (-(E + 1)) := by ring
    _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

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

theorem exists_allocated_original_site_selected
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
              AllocatedOriginalSiteSelectedAt.{_, _, _, uGeom, uCover, uSpace}
                (G := G) (dim := dim) B D Psp E e t A₀ T₀ Kproj K Kbuf := by
  have hE1 : 0 ≤ E + 1 := by linarith
  let target := profileReferenceErrorLog Psp (E + 1 + 4)
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he : 0 ≤ physicalIdealSmoothingLog (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
      hLayer A T target (allocatedProfileGainLog m D Psp w) :=
    physicalIdealSmoothingLog_nonneg hLayer A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj, hselected⟩ :=
    exists_allocated_original_selected_ideal.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE1
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    allocatedOriginalSelectedAt_site B hdim hPsp hE he ht1 hT₀ hδ hδ1 hδe hselected⟩

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

theorem exists_allocated_original_ambient_selected
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
              AllocatedOriginalAmbientSelectedAt.{_, _, _, uGeom, uCover, uSpace}
                (G := G) (dim := dim) B D Psp E e t A₀ T₀ Kproj K Kbuf := by
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
      Kbuf, hKbuf, hselected⟩ :=
    exists_allocated_original_site_selected.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    Kbuf, hKbuf, allocatedOriginalSiteSelectedAt_ambient B hdim ht1 hselected⟩

end Erdos3.VectorPolynomial

end

end OAI
