import OAI.Combinatorics.Progressions.Probability.AllocatedRecenteredSeparatedMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

theorem allocatedWholeProfile_recentered_primitive_coarsening
    {p₁ w v : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hp₁four : 4 ≤ p₁)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁) :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
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
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (_hW : 0 ≤ W) (ξ : ℝ), 0 < ξ →
    let H := trimmedSpatialRootScale ρ N stride
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
        Option (Fin dim) → ZMod (residueRefinedPeriod q stride)) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    ∀ (M : ℕ) (hM : 0 < M) (selection : Fin dim ↪ G)
      (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
      (Qsp : ℝ≥0), 1 ≤ Qsp → (1 + W) / (S.value : ℝ) ≤ Qsp →
      allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W →
      (integerScalarLattice (Unit ⊕ Fin dim) (q : ℤ) ≤
        pivotFullImage
          (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (Z ε : ℝ), 0 < Z → Z⁻¹ ≤ 2 → 0 < ε →
    let Vmass := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((Qsp : ℝ) ^ dim) ^ Fintype.card X) *
      Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1) * 2
    let coarse := allocatedRecenteredCoarseMesh (M := M) X q selection Qsp Vmass ε
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ z, ‖test z‖ ≤ 1) →
      ‖law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
          B U b S X q stride reference x hM selection hx N _hW fine base cells point test profile) / (Z : ℂ) -
        law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
          B U b S X q stride reference x hM selection hx N _hW coarse base cells point test profile) / (Z : ℂ)‖ ≤ ε := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW ξ hξ H law point profile
    reference base cells V₀ hZ₀ hrows hscale M hM selection hx Qsp hQsp hratio hrootBudget hspatial
    Z ε hZ hZi hε Vmass coarse
  let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
    (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
  have hprevious := allocatedWholeProfile_recentered_primitive_mass B U b hR hσ S q
    hp₁ hw hv hp₁four hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ (K := K) hSampling
  have hMass := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp
    hmask hperiod C V hC hV hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _
    p hp hmp stride hs R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW ξ hξ
    reference base cells hZ₀ hrows hscale
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  obtain ⟨y, _hy⟩ := law.exists_weight_pos
  have hroot (g : G) : |((x g none : ℤ) : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hrootBudget
    have hroot : |((x g none : ℤ) : ℝ)| ≤ W := by
      simpa only [allocatedPhysicalCubeRoot, Sum.elim_inl, zero_add] using h
    linarith
  have hfactor : factor ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((Qsp : ℝ) ^ dim) ^ Fintype.card X) := by
    dsimp only [factor]
    have hratio0 : 0 ≤ (1 + W) / (S.value : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
    have hbase : 0 ≤ 30 / smoothProbabilityProfile 0 := div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le
    gcongr
  have hprofile0 : 0 < smoothProbabilityProfile 0 := smoothProbabilityProfile_pos_zero
  have hMassBound : law.mean (allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X q stride reference x N base cells point profile) / Z ≤ Vmass := by
    apply (div_le_div_of_nonneg_right hMass hZ.le).trans
    rw [div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le) hZi
      (inv_nonneg.mpr hZ.le) (by positivity)
  exact allocatedRecenteredReference_coarse_comparison B U b S X q stride reference x
    hM selection hx N hW base cells point hs hN hρ profile Qsp hQsp hratio hroot hspatial
    Z Vmass ε hZ hε hMassBound

end Erdos3.VectorPolynomial

end

end OAI
