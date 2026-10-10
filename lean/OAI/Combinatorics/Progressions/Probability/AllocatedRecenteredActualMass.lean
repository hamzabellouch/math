import OAI.Combinatorics.Progressions.Dynamics.AllocatedRecenteredErrorBudget
import OAI.Combinatorics.Progressions.Sampling.AllocatedRecenteredSamplingData

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_recentered_certified_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (wholeReference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
      Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    {Perr : ℝ} (_hPerr : 0 ≤ Perr)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Perr)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Perr) (_hn : ∀ j, (n j : ℝ) ≤ Perr)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ Perr)
    (_hMPerr : (M : ℝ) ≤ Real.exp Perr) (_hSP : (S.value : ℝ) ≤ Real.exp Perr)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp Perr) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp Perr)
    (_hBudget : allocatedErrorFourierOutput m Perr ≤ P)
    (η : ℝ≥0) (_hη1NN : η ≤ 1) {δf : ℝ} (_hδf : 0 < δf) (_hδfP : δf⁻¹ ≤ Real.exp Perr),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (Afourier : ℕ) {Pfourier : ℝ} (_hPfourier : 0 ≤ Pfourier)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier Pfourier)
    (_hmf : (m : ℝ) ≤ Pfourier)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pfourier)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp Pfourier) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp Pfourier)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ Pfourier)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pfourier) (_hnf : ∀ j, (n j : ℝ) ≤ Pfourier)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pfourier)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pfourier)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp Pfourier) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp Pfourier)
    (_hFourierBudget : allocatedJetFourierBudget m dim Afourier Pfourier ≤ P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Ec Tc : ℝ} (_hPc : 0 ≤ Pc) (_hEc : 0 ≤ Ec) (_hTc : 0 ≤ Tc)
    (_hη : 0 < (η : ℝ))
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hηE : (η : ℝ)⁻¹ ≤ Real.exp Ec)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc Ec Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1) → ℝ) → ℝ)
    (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ))
    (_hmasks : ∀ u r j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ≤ Cm)
    {δp Lp : ℝ} (_hδp : 0 < δp) {Z : ℝ} (_hZ : 0 < Z)
    (Mprofile : ℝ)
    (_hdata : AllocatedProfileSamplingData B U b S
      (fun u => allocatedContinuousLongJetProxy B U b S x u jetRows s hA) (fun _ => f)
      (Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n))
      C V δp Mprofile Lp P),
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    let mass := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean
      (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells (physicalCubeEuclideanSample U d p hm)
        (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d y modulus f z : ℂ)))
    mass / Z ≤ (coarseReferenceMassConstant dim X W S.value +
      Vsp * ((Merr + 2 * δf + ε) + (Mprofile + 2 * δp + ε))) / Z ∧
    ∀ {Pbound D : ℝ}, 0 ≤ Pbound → ((dim + 1 : ℕ) : ℝ) ≤ Pbound →
      (Fintype.card X : ℝ) ≤ Pbound → D ≤ Real.exp Pbound → W ≤ D * S.value →
      Z⁻¹ ≤ 2 → (Merr + 2 * δf + ε) + (Mprofile + 2 * δp + ε) ≤ 1 →
      mass / Z ≤ Real.exp (coefficientErrorVolumeLog Pbound + 4) := by
  obtain ⟨K, hK, hmassBound⟩ := exists_allocated_recentered_sampling_data_mass_bound m dim
  obtain ⟨T, hT, hproject⟩ := exists_allocated_retained_reference_mass m dim
  refine ⟨max K T, hK.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference wholeReference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    M hM selection hx hdimc hmod Perr hPerr hvars hI hn hJ hMPerr hSP hCP hVP hBudget
    η hη1NN δf hδf hδfP A hRefined instRefined
    s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw
    hgi hgm Afourier Pfourier hPfourier hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf hFourierBudget
    hσ1 Pc Ec Tc hPc hEc hTc hη hMP hRP hRi hσi hcount hηE hlarge hi hbound
    f Cm hCm hmasks δp Lp hδp Z hZ Mprofile hdata Vsp Merr mass
  have hKcut : Real.exp ((P + K)^K) ≤ Real.exp ((P + (max K T : ℕ))^max K T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega) (le_max_left _ _))
  have hTcut : Real.exp ((P + T)^T) ≤ Real.exp ((P + (max K T : ℕ))^max K T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega) (le_max_right _ _))
  have hprojected := hproject B U b S (fun _ => 0) x C V d (NeZero.pos d) g ν hg0 hgi hgm
    Afourier hPfourier hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hFourierBudget hX hdim p hp hm N q hq hW hτ hξ1 hρ hτP hstride
    (fun t => hTcut.trans (hsize t)) hrank (hTcut.trans hRank) hsizeSp hρ8 hρshift
  obtain ⟨hL, _hp, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedErrorPrimitive_fourier_budget B U b S jetRows hdimc (fun _ => Subtype.val_injective)
      hb bW M modulus hmod η C V hPerr hvars hI hn hJ hη1NN hMPerr hSP hCP hVP hδfP
  have hpoint u r z := allocatedFixedKernel_refined_pointwise B U b hR hσ S x jetRows
    hM selection hx hdimc (fun _ => Subtype.val_injective) (fun _ z => z.property) hσ1
    hPc hEc hTc hη hη1NN hMP hRP hRi hσi hcount hηE hlarge
    modulus hperiod s hA hi (residueRefinedPeriod modulus q) hRefined hbound u r hlengths
    (residue u r) (hr u r) z
  exact hmassBound B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference wholeReference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass p hp hm
    hP hX hdim hτP hstride hε hεP (fun t => hKcut.trans (hsize t)) hrank (hKcut.trans hRank)
    η hδf hL hamb hδL hLip (hfreq.trans (Real.exp_le_exp.mpr hBudget))
    (hcoeff.trans (Real.exp_le_exp.mpr hBudget)) hRefined s hA residue hlengths href hr
    Cinv hCinv hchart hsmall μ g hg hg0 hlaw (fun y y₀ a => hprojected y y₀ base a)
    hσ1 hpoint f Cm hCm hmasks hδp hZ Mprofile hdata

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_recentered_accuracy_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (Afourier : ℕ) {P pB E Ptotal : ℝ} (_hP : 0 ≤ P) (_hpB : 0 ≤ pB) (_hE : 0 ≤ E)
    (_hTotal : allocatedUnifiedSamplingBudget m dim Afourier P pB E ≤ Ptotal)
    (_hpP : pB ≤ P) (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (wholeReference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
      Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {Rrank : ℝ}
    (_hτP : 1 / τ ≤ Real.exp (Ptotal)) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp (Ptotal))
    (_hsize : ∀ t, Real.exp (((Ptotal) + K)^K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp (((Ptotal) + K)^K) ≤ Rrank)
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    (_hdimB : ((dim+1 : ℕ) : ℝ) ≤ pB)
    (_hvarsB : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pB)
    (_hIB : ∀ j, (Fintype.card (I j) : ℝ) ≤ pB) (_hnB : ∀ j, (n j : ℝ) ≤ pB)
    (_hJB : ∀ j, (Fintype.card (J j) : ℝ) ≤ pB) (_hXB : (Fintype.card X : ℝ) ≤ pB)
    (_hMPB : (M : ℝ) ≤ Real.exp pB) (_hCPB : ∀ j, (C j : ℝ) ≤ Real.exp pB),
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier P)
    (_hmf : (m : ℝ) ≤ P)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hnf : ∀ j, (n j : ℝ) ≤ P)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Tc : ℝ} (_hPc : 0 ≤ Pc) (_hTc : 0 ≤ Tc)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc (allocatedCoefficientAccuracyLog m pB (E+3)) Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z D : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2)
    (_hD : D ≤ Real.exp pB) (_hWD : W ≤ D * S.value)
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1) → ℝ) → ℝ)
    (Lprofile : ℝ),
    let Cm : ℝ≥0 := ⟨(layerKernelIndexBound m M : ℝ), Nat.cast_nonneg _⟩
    let a := allocatedCoefficientAccuracy m pB (E + 3)
    AllocatedProfileSamplingData B U b S
      (fun u => allocatedContinuousLongJetProxy B U b S x u jetRows s hA) (fun _ => f)
      (Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n))
      C V a (Real.exp (-(E + 3))) Lprofile Ptotal →

    let mass := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean
      (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells (physicalCubeEuclideanSample U d p hm)
        (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d y modulus f z : ℂ)))
    mass / Z ≤ Real.exp (coefficientErrorVolumeLog pB + 4) := by
  obtain ⟨K, hK, hcertified⟩ := exists_allocated_recentered_certified_mass_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V
    Afourier P pB E Ptotal hP hpB hE hTotal hpP hSP hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference wholeReference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass poly hpoly hm Rrank hτP hstride hsize hrank hRank
    M hM selection hx hdimc hmod hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined instRefined s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw
    hgi hgm hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 Pc Tc hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound Z D hZ hZi hD hWD f Lprofile Cm a hdata mass
  let Pmass := Ptotal
  let Perr := allocatedTupleErrorBudget m P pB E
  have hE3 : 0 ≤ E+3 := by linarith only [hE]
  have ha := allocatedCoefficientAccuracy_bounds m hpB hE3
  obtain ⟨hPerr, hPPerr, hAccuracy, hPmass₀, hScalar₀, _hWidth, _hPplus, hpMass₀, _hEMass, hDimMass₀⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim Afourier hP hpB hE
  have hPmass : 0 ≤ Pmass := hPmass₀.trans hTotal
  have hScalar := hScalar₀.trans hTotal
  have hpMass := hpMass₀.trans hTotal
  have hDimMass := hDimMass₀.trans hTotal
  have hs := allocatedScalarSamplingBudget_bounds m dim Afourier hP hPerr
  have hPerrMass : Perr ≤ Pmass := hs.2.2.2.trans hScalar
  have hFourierBudget := hs.2.1.trans hScalar
  have hErrorBudget := hs.2.2.1.trans hScalar
  have hpErr : pB ≤ Perr := hpP.trans hPPerr
  have hainvErr : a⁻¹ ≤ Real.exp Perr := ha.2.2.le.trans (Real.exp_le_exp.mpr hAccuracy)
  have hainvMass : 1/a ≤ Real.exp Pmass := by
    simpa only [one_div] using hainvErr.trans (Real.exp_le_exp.mpr hPerrMass)
  have hlog : 0 ≤ allocatedCoefficientAccuracyLog m pB (E+3) :=
    neg_nonpos.mp (Real.exp_le_one_iff.mp ha.2.1)
  have hXmass : (Fintype.card X : ℝ) ≤ Pmass := hXB.trans hpMass
  have hdimMass : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass := by
    apply le_trans _ hDimMass
    have hd : (dim : ℝ)+1 ≤ pB := by exact_mod_cast hdimB
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    have hh := mul_le_mul hd hXB (Nat.cast_nonneg (Fintype.card X)) hpB
    nlinarith only [hh, hpB]
  have hCm : 1 ≤ (Cm : ℝ) := by
    change (1 : ℝ) ≤ (layerKernelIndexBound m M : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (pow_pos hM (m * 2 ^ (m + 1)))
  have hmasks u r j z := allocatedIntegerKernelMask_bound B U b S x jetRows hM selection hx
    hdimc (fun _ => Subtype.val_injective) (fun _ z => z.property) j modulus (residue u r j) z
  let η : ℝ≥0 := ⟨a, ha.1.le⟩
  have hresult := hcertified B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference wholeReference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass poly hpoly hm
    hPmass hXmass hdimMass hτP hstride ha.1 hainvMass hsize hrank hRank
    hM selection hx hdimc hmod hPerr
    (hvarsB.trans hpErr) (fun j => (hIB j).trans hpErr) (fun j => (hnB j).trans hpErr)
    (fun j => (hJB j).trans hpErr) (hMPB.trans (Real.exp_le_exp.mpr hpErr))
    (hSP.trans (Real.exp_le_exp.mpr hPPerr))
    (fun j => (hCPB j).trans (Real.exp_le_exp.mpr hpErr))
    (fun j => (hVPf j).trans (Real.exp_le_exp.mpr hPPerr)) hErrorBudget η ha.2.1 ha.1 hainvErr
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw
    hgi hgm Afourier hP hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf hFourierBudget
    hσ1 hPc hlog hTc ha.1 hMP hRP hRi hσi hcount ha.2.2.le hlarge hi hbound
    f Cm hCm hmasks ha.1 hZ (Real.exp (-(E + 3))) hdata
  apply hresult.2 hpB hdimB hXB hD hWD hZi
  have herror := allocatedRecenteredErrorFactor_le B U b hb bW jetRows
    (by simpa only [Fintype.card_fin] using hdimc) (fun _ => Subtype.val_injective) C hpB hE
    hvarsB hIB hnB hJB hCPB hMPB hmod (Real.exp (-(E + 3))) le_rfl
  have herrorOne := herror.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hE))
  rw [Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg jets Q modulus)]
  change a * coefficientDeckPeriodCap jets Q modulus *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ ax : LayerSamplerAxis I n, jets ax.1) + 2 * a + a +
      (Real.exp (-(E + 3)) + 2 * a + a) ≤ 1
  simpa only [mul_assoc] using herrorOne

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

variable (m dim : ℕ)
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_uniform_allocated_recentered_actual_mass :
    ∃ K : ℕ, 2 ≤ K ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (_hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (_hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (_hLip : LipschitzWith A ψ) (_hTransition : LipschitzWith T Real.smoothTransition)
    {D0 pB E : ℝ} (_hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D0)
    (_hpB : 0 ≤ pB) (_hE : 0 ≤ E),
      let target := profileReferenceErrorLog pB E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * pB
      let gainLog := allocatedProfileGainLog m D0 pB w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a)) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
    ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (Afourier : ℕ) {P : ℝ} (_hP : 0 ≤ P)
    (_hpP : pB ≤ P) (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (wholeReference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
      Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {M : ℕ} (_hM : 0 < M) (selection : Fin dim ↪ G)
    (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    (_hdimB : ((dim+1 : ℕ) : ℝ) ≤ pB)
    (_hvarsB : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pB)
    (_hIB : ∀ j, (Fintype.card (I j) : ℝ) ≤ pB) (_hnB : ∀ j, (n j : ℝ) ≤ pB)
    (_hJB : ∀ j, (Fintype.card (J j) : ℝ) ≤ pB) (_hXB : (Fintype.card X : ℝ) ≤ pB)
    (_hMPB : (M : ℝ) ≤ Real.exp pB) (_hCPB : ∀ j, (C j : ℝ) ≤ Real.exp pB),
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier P)
    (_hmf : (m : ℝ) ≤ P)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hnf : ∀ j, (n j : ℝ) ≤ P)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Tc : ℝ} (_hPc : 0 ≤ Pc) (_hTc : 0 ≤ Tc)
    (_hpBc : pB ≤ Pc) (_hVPc : ∀ j, (V j : ℝ) ≤ Real.exp Pc)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc (allocatedCoefficientAccuracyLog m pB (E+3)) Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z D : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2)
    (_hD : D ≤ Real.exp pB) (_hWD : W ≤ D * S.value)
    (_hmeshLarge : Real.exp (target + (gainLog + allocatedIdealMeshEnvelope m D0 Pc e) + 3) ≤
      (S.value : ℝ)) {Rrank : ℝ},
    let input := allocatedActualProfileInput m D0 Pc e gainLog P
    let L0 := allocatedProfileFourierInput input
    let P0 := allocatedProfileFourierOutput input
    let accuracyLog := allocatedCoefficientAccuracyLog m pB (E + 3)
    let Ptotal := max (allocatedUnifiedSamplingBudget m dim Afourier P pB E)
      (allocatedProfileAccuracyBudget L0 P0 accuracyLog)
    1 / τ ≤ Real.exp Ptotal →
    (∀ t, (q t : ℝ) ≤ Real.exp Ptotal) →
    (∀ t, Real.exp ((Ptotal + K) ^ K) ≤ (N t : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j)) →
    Real.exp ((Ptotal + K) ^ K) ≤ Rrank →
    let f := physicalActiveProfileIdeal (G := G) (B := B) (G × Option (Fin dim)) (layerSamplerDegree I n)
      (allocatedGridAxis (I := I) U b S.value) (fun a => jetRows a.val.1)
      (fun a => R a.1) (fun a => hR a.1) δ
    let mass := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean
      (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells (physicalCubeEuclideanSample U d p hm)
        (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d y modulus f z : ℂ)))
    mass / Z ≤ Real.exp (coefficientErrorVolumeLog pB + 4) ∧
      (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W →
      (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage
          (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
      ∀ ε : ℝ, 0 < ε →
      let whole := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
      let point := physicalCubeEuclideanSample U d p hm
      let profile := fun y z =>
        (allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d y modulus f z : ℂ)
      let coarse := allocatedRecenteredCoarseMesh (M := M) X modulus selection
        (allocatedPrimitiveRootRatio (Real.exp pB)) (Real.exp (coefficientErrorVolumeLog pB + 4)) ε
      0 < coarse ∧ coarse ≤ 1 / 4 ∧
        ∀ fine : ℝ, 0 < fine → fine ≤ coarse →
        ∀ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ, (∀ z, ‖test z‖ ≤ 1) →
        ‖whole.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
            B U b S X modulus q wholeReference x _hM selection _hx N _hW fine base cells point test profile) / (Z : ℂ) -
          whole.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
            B U b S X modulus q wholeReference x _hM selection _hx N _hW coarse base cells point test profile) / (Z : ℂ)‖ ≤ ε) := by
  obtain ⟨K, hK, hmass⟩ :=
    exists_allocated_recentered_accuracy_mass_bound.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ ψ hψ hrange hzero hone A T hLip hTransition D0 pB E hdim hpB hE
  let target := profileReferenceErrorLog pB E
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hpB
    dsimp [target, profileReferenceErrorLog]
    linarith only [hs, hE]
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * pB
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hpB
  let gainLog := allocatedProfileGainLog m D0 pB w
  have hgainLog : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hpB hw
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg (layerSamplerDegree I n) A T htarget hgainLog
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcontrol⟩ :=
    exists_allocated_actual_profile_sampling_data (G := G) (α := Fin dim) (O := jets) B
      ψ hψ hrange hzero hone A T hLip hTransition hdim htarget hpB hw
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro J _ U b R σ hR hσ hσt S x _ hb o Q _ bW d _ C V Afourier P hP hpP hSP hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference wholeReference N hN W τ ξ ρ hW hτ hξ hξ1 hρ
    hsizeSp hρ8 hρshift base cells hselected poly hpoly hm
    M hM selection hx hdimc hmod hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined instRefined s hA block residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _
    g hg hg0 hlaw hgi hgm hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 Pc Tc hPc hTc hpBc hVPc hMP hRP hRi hσi hcount hlarge hi hbound Z D hZ hZi hD hWD
    hmeshLarge Rrank input L0 P0 accuracyLog Ptotal hτP hstride hsize hrank hRank f mass
  let Cm : ℝ≥0 := ⟨(layerKernelIndexBound m M : ℝ), Nat.cast_nonneg _⟩
  have hCmw : (Cm : ℝ) ≤ Real.exp w := layerKernelIndexBound_le_exp m hMPB
  have hD0 : 0 ≤ D0 := hdim.nonneg
  have hgrid := allocatedIdealGridEnvelope_nonneg m hD0 hPc he
  have hmeshCost : 0 ≤ gainLog + allocatedIdealMeshEnvelope m D0 Pc e := by
    unfold allocatedIdealMeshEnvelope
    positivity
  have hmesh0 := (physicalIdealErrorShare_pos target
    (gainLog + allocatedIdealMeshEnvelope m D0 Pc e)).le
  have hmesh1 := physicalIdealErrorShare_le_one htarget hmeshCost
  have hmesh := physicalIdealErrorShare_scale_mesh (layerTailDegree m) htarget hmeshCost hmeshLarge
  have hunit : (1 : ℝ)⁻¹ ≤ Real.exp Pc := by simpa only [inv_one] using Real.one_le_exp hPc
  obtain ⟨_hP0, hdata⟩ := hcontrol U b hR hσ hσt S x jetRows
    (fun _ => Subtype.val_injective) (fun _ z => z.property) block s hA hM hi
    hPc hMP hRP hRi hσi hcount hmesh0 hmesh1 hmesh le_rfl hb o bW modulus hmod hMPB
    Cm hCmw hP hSP C V (fun j => (hCPB j).trans (Real.exp_le_exp.mpr hpBc)) hVPc hunit
  have hE3 : 0 ≤ E + 3 := by linarith only [hE]
  have ha := allocatedCoefficientAccuracy_bounds m hpB hE3
  have hlog : 0 ≤ accuracyLog := neg_nonpos.mp (Real.exp_le_one_iff.mp ha.2.1)
  have haccurate := allocatedProfileSamplingData_accuracy B U b S
    (fun u => allocatedContinuousLongJetProxy B U b S x u jetRows s hA) (fun _ => f)
    (Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n))
    C V hdata hlog ha.2.2.le
  have hcommon := allocatedProfileSamplingData_reference_accuracy B U b S
    (fun u => allocatedContinuousLongJetProxy B U b S x u jetRows s hA) (fun _ => f)
    (Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n))
    C V (P' := Ptotal) haccurate hpB (le_max_right _ _)
  have hactualMass := hmass B U b hR hσ S x hb o bW d C V Afourier hP hpB hE (le_max_left _ _) hpP hSP hC hV
    ν modulus hperiod q hq reference wholeReference N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hselected poly hpoly hm hτP hstride hsize hrank hRank
    hM selection hx hdimc hmod hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw hgi hgm
    hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound hZ hZi hD hWD f (L0 + accuracyLog) hcommon

  refine ⟨hactualMass, ?_⟩
  intro hrootBudget hspatial ε hε whole point profile coarse
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hratio : (1 + W) / (S.value : ℝ) ≤ allocatedPrimitiveRootRatio (Real.exp pB) := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos pB).le).1]
    apply (div_le_iff₀ hS).mpr
    have hWExp := hWD.trans (mul_le_mul_of_nonneg_right hD hS.le)
    nlinarith only [hWExp, hS1]
  obtain ⟨y, _hy⟩ := whole.exists_weight_pos
  have hroot (g₀ : G) : |((x g₀ none : ℤ) : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g₀)).trans hrootBudget
    have h' : |((x g₀ none : ℤ) : ℝ)| ≤ W := by
      simpa only [allocatedPhysicalCubeRoot, Sum.elim_inl, zero_add] using h
    linarith only [h']
  exact allocatedRecenteredReference_coarse_comparison B U b S X modulus q wholeReference x
    hM selection hx N hW base cells point hq hN hτ profile (allocatedPrimitiveRootRatio (Real.exp pB))
    (allocatedPrimitiveRootRatio_bounds (Real.exp_pos pB).le).2.1 hratio hroot hspatial
    Z (Real.exp (coefficientErrorVolumeLog pB + 4)) ε hZ hε hactualMass

end Erdos3.VectorPolynomial

end

end OAI
