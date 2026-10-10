import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source
import OAI.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
import OAI.Combinatorics.Progressions.Sampling.AllocatedFiniteModelSquareSampling

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uE uT uF

open Module Submodule _root_.Set _root_.OAI.Set MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type uE} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem allocated_finite_model_reconstruction_source
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type uT} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)

    {A : ℕ} (hSampling : PhysicalModelSquareSampling.{0, uJ, uF, max uE uT uI} m A)
    {X : Type} [Fintype X] [DecidableEq X]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j ex, coefficients (p j) ex ∈ U j)
    {P target : ℝ} (hP : 0 ≤ P) (htarget : 0 ≤ target)
    (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hdP : (d : ℝ) ≤ Real.exp P)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (hsP : ∀ t, (stride t : ℝ) ≤ Real.exp P)
    {Rrank ρ : ℝ} (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P)
    (H : X → ℝ) (hH : ∀ t, Real.exp ((P + target + A) ^ A) ≤ H t)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rrank (U j) (p j))
    (hRank : Real.exp ((P + target + A) ^ A) ≤ Rrank)
    {Ksp : Type*} [Fintype Ksp]
    (root : Ksp → ℤ) (D : Matrix (Fin dim) Ksp ℤ)
    (cells : Finset (ColumnResiduePattern (Option Ksp) X stride))
    (widths : Option Ksp × X → ℝ) (hwidths : ∀ z, 0 < widths z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (Hwindow : X → ℝ) (hHwindow : ∀ t, 1 ≤ Hwindow t)
    (hwidth : ∀ z : Option (Fin dim) × X, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    (base : X → ℤ)
    (Twindow : X → ℝ) (hTwindow : ∀ t, 0 < Twindow t)
    {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ t, Hwindow t = (1 + Wsp) * Twindow t)
    (hrows : ∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ Hwindow t)
    (hprofile : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow t)
    (ψ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ spatialWindow (α := Fin dim) Hwindow 4, ‖ψ w‖ ≤ Cψ)
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ : ℝ} (hδ : 0 ≤ δ)
    {F : Type uF} [Fintype F] (c : F → ℂ)
    (factor : F → (CoefficientAmbientIndex (Fin dim) J → UnitAddCircle) → ℂ)
    (Lf : F → ℝ≥0) (hfactor : ∀ t, LipschitzWith (Lf t) (factor t))
    (hfactorb : ∀ t z, ‖factor t z‖ ≤ 1) (hLf : ∀ t, (Lf t : ℝ) ≤ Real.exp P)
    (density : EuclideanJetLayers U rowTypes → ℂ) (hden : Measurable density) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    let model := fun y => allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y
    let window := spatialWindow (α := Fin dim) Hwindow 4
    let scale := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (Hwindow t) (Twindow t) Lsp i : ℝ)
    let reconstruct := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative stride a.val) stride
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
    (∀ k, (period * commonSitePeriod e k : ℕ) ≤ Real.exp P) →
    (∀ k, ((Fintype.card (Finset (Fin dim)) * ((Llong + Lgrid k) * (period * commonSitePeriod e k) *
      ((∑ j : Fin m, ((rowSets j).card : ℝ≥0)) *
        ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0))) : ℝ≥0) : ℝ) ≤ Real.exp P) →
    (∑ t, ‖c t‖) + (∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))), ∑ i, ∑ k,
      ‖(((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
          coverSiteCoefficient e k)‖) ≤ Real.exp P →
    Measurable model →
    Integrable (fun y => ‖density y - model y‖ ^ 2)
      (Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) →
    (∫ y, ‖density y - model y‖ ^ 2
      ∂Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) ≤ Real.exp (-(target + 20)) →
    (∀ z : CoefficientTorus (K := Fin dim) U,
      ‖density (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows z) -
        ∑ t, c t * factor t (coefficientAmbientTorus U z)‖ ≤ Real.exp (-(target + 20))) →
    κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells widths t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) *
        density (physicalCubeRowSample U d rows p hm (reconstruct t.1 t.2.val))).re →
    (Cψ * ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X)) *
        (Cψ * (volumeFactor * Real.exp (-target))) ≤ δ ^ 2 →
    κ - δ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells widths t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) *
        model (physicalCubeRowSample U d rows p hm (reconstruct t.1 t.2.val))).re := by
  intro Lcoord Llong Lgrid model window scale reconstruct volumeFactor
    hperiodP htermLip hmass hmod hint hL2 happ hsource hcost
  apply physicalReconstruction_source_of_sampled_square_geometric stride hs root D base cells widths
    hwidths hZ Hwindow Twindow (fun t => lt_of_lt_of_le zero_lt_one (hHwindow t)) hTwindow hLsp hsc
    hrows hprofile ψ test (fun w => density (physicalCubeRowSample U d rows p hm w))
    (fun w => model (physicalCubeRowSample U d rows p hm w)) hCψ hψ htest ?_ hsource hδ hHwindow hcost
  intro cell
  exact allocated_finite_model_reference_sample B U b S x y₀ q d period r hr hb o bW e
    hdiv hR C hC hchart hbudget Cforward hforward K hK a f hf hf1 he Q hQ
    hSampling μ ν p hp hm hP htarget hn hdim hamb hdP stride hs hsP hρ hρP H hH hrank hRank
    {columnResiduePattern stride (standardPhysicalCubeFrame
      (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride cell.val)))}
    (Finset.singleton_nonempty _) Hwindow hHwindow hwidth base c factor Lf hfactor hfactorb hLf density hden
    hperiodP htermLip hmass hmod hint hL2 happ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uE uT uF

open Module Submodule _root_.Set _root_.OAI.Set MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type uE} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem allocated_projected_finite_model_source
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type uT} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)

    {X : Type} [Fintype X] [DecidableEq X]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j ex, coefficients (p j) ex ∈ U j)
    {P target : ℝ} (hP : 0 ≤ P) (htarget : 0 ≤ target)
    (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hdP : (d : ℝ) ≤ Real.exp P)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (hsP : ∀ t, (stride t : ℝ) ≤ Real.exp P)
    {Rrank ρ : ℝ} (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P)
    (H : X → ℝ) (hH : ∀ t, Real.exp ((P + target + physicalModelSamplingExponent.{0, uJ, 0, max uE uT uI} m) ^
      physicalModelSamplingExponent.{0, uJ, 0, max uE uT uI} m) ≤ H t)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rrank (U j) (p j))
    (hRank : Real.exp ((P + target + physicalModelSamplingExponent.{0, uJ, 0, max uE uT uI} m) ^
      physicalModelSamplingExponent.{0, uJ, 0, max uE uT uI} m) ≤ Rrank)
    {Ksp : Type*} [Fintype Ksp]
    (root : Ksp → ℤ) (D : Matrix (Fin dim) Ksp ℤ)
    (cells : Finset (ColumnResiduePattern (Option Ksp) X stride))
    (widths : Option Ksp × X → ℝ) (hwidths : ∀ z, 0 < widths z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (Hwindow : X → ℝ) (hHwindow : ∀ t, 1 ≤ Hwindow t)
    (hwidth : ∀ z : Option (Fin dim) × X, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    (base : X → ℤ)
    (Twindow : X → ℝ) (hTwindow : ∀ t, 0 < Twindow t)
    {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ t, Hwindow t = (1 + Wsp) * Twindow t)
    (hrows : ∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ Hwindow t)
    (hprofile : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow t)
    (ψ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ spatialWindow (α := Fin dim) Hwindow 4, ‖ψ w‖ ≤ Cψ)
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ : ℝ} (hδ : 0 ≤ δ)
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ)
    (hgm : ∀ y, Measurable (g y))
    (Cfourier Lfourier : ℝ≥0)
    (hFourierLip : ((Fintype.card (CoefficientAmbientIndex (Fin dim) J) *
      (CircleFourier.characterLipConstant * Lfourier) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hFourier : ∀ y, ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (frequency : F → ∀ j, (Fin dim →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
        (∀ t j ex, ex.degree ≤ j.val + 1 → ∀ i, |(frequency t j ex i : ℝ)| ≤ Lfourier) ∧
        (∑ t, ‖coeff t‖) ≤ Cfourier ∧
        ∀ z, ‖(g y (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤
          Real.exp (-(target + 20))) :
    let density := physicalRowsProjectedMean U law g
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    let model := fun y => allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y
    let window := spatialWindow (α := Fin dim) Hwindow 4
    let scale := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (Hwindow t) (Twindow t) Lsp i : ℝ)
    let reconstruct := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative stride a.val) stride
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
    (∀ k, (period * commonSitePeriod e k : ℕ) ≤ Real.exp P) →
    (∀ k, ((Fintype.card (Finset (Fin dim)) * ((Llong + Lgrid k) * (period * commonSitePeriod e k) *
      ((∑ j : Fin m, ((rowSets j).card : ℝ≥0)) *
        ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0))) : ℝ≥0) : ℝ) ≤ Real.exp P) →
    (Cfourier : ℝ) + (∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))), ∑ i, ∑ k,
      ‖(((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
          coverSiteCoefficient e k)‖) ≤ Real.exp P →
    Measurable model →
    Integrable (fun y => ‖density y - model y‖ ^ 2)
      (Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) →
    (∫ y, ‖density y - model y‖ ^ 2
      ∂Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) ≤ Real.exp (-(target + 20)) →
    κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells widths t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) *
        density (physicalCubeRowSample U d rows p hm (reconstruct t.1 t.2.val))).re →
    (Cψ * ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X)) *
        (Cψ * (volumeFactor * Real.exp (-target))) ≤ δ ^ 2 →
    κ - δ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells widths t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) *
        model (physicalCubeRowSample U d rows p hm (reconstruct t.1 t.2.val))).re := by
  intro density Lcoord Llong Lgrid model window scale reconstruct volumeFactor
    hperiodP htermLip hmass hmod hint hL2 hsource hcost
  have hSampling : PhysicalModelSquareSampling.{0, uJ, 0, max uE uT uI} m
      (physicalModelSamplingExponent.{0, uJ, 0, max uE uT uI} m) :=
    (physicalModelSamplingExponent_spec.{0, uJ, 0, max uE uT uI} m).2
  obtain ⟨F, inst, c, factor, hc, hfactors, hfb, happ⟩ :=
    exists_physicalRowsProjectedMean_unit_expansion U law g Cfourier Lfourier hFourier
  let _ := inst
  exact allocated_finite_model_reconstruction_source B U b S x y₀ q d period r hr hb o bW e
    hdiv hR C hC hchart hbudget Cforward hforward K hK a f hf hf1 he Q hQ
    hSampling μ ν p hp hm hP htarget hn hdim hamb hdP stride hs hsP hρ hρP H hH hrank hRank
    root D cells widths hwidths hZ Hwindow hHwindow hwidth base Twindow hTwindow hLsp hsc hrows hprofile
    ψ test hCψ hψ htest hδ c factor
    (fun _ => Fintype.card (CoefficientAmbientIndex (Fin dim) J) * (CircleFourier.characterLipConstant * Lfourier))
    hfactors hfb (fun _ => hFourierLip) density (physicalRowsProjectedMean_measurable U law g hgm)
    hperiodP htermLip (by linarith only [hc, hmass]) hmod hint hL2 happ hsource hcost

end Erdos3.VectorPolynomial

end

end OAI
