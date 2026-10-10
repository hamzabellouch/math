import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source
import OAI.Combinatorics.Progressions.Estimates.PhysicalL1SourceAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type uO} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hinj : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" => physicalCubeRowSample U cover rows poly hm
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
include hinj hcard hp μ in
theorem allocatedRecenteredSelectedMean_rank_l1_source
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (ideal model : EuclideanJetLayers U O → ℂ)
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ ε : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfb : ∀ z, ‖f z‖ ≤ Cf) (hgb : ∀ z, ‖g z‖ ≤ Cg)
    (hactual : ∀ y, law.complexMean (fun a => profile a y) = f (coveredJetAmbientTorus U 1 y))
    (hi : Measurable ideal) {P Rrank S₀ η εsample δsur Eerror : ℝ}
    (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp P)
    (hS₀ : 0 ≤ S₀) (hS₀P : S₀ ≤ Real.exp P) (hstride : ∀ i, (q i : ℝ) ≤ S₀)
    (hτP : 1 / τ ≤ Real.exp P) (hεsample : 0 < εsample) (hεsampleP : 1 / εsample ≤ Real.exp P)
    (hsize : ∀ i, Real.exp ((P + (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ^ (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((P + (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ^ (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ≤ Rrank)
    (hη : 0 < η) (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hLf : (Lf : ℝ) ≤ Real.exp P) (hLg : (Lg : ℝ) ≤ Real.exp P)
    (hCf : (Cf : ℝ) ≤ Real.exp P) (hCg : (Cg : ℝ) ≤ Real.exp P)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P)
    (happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δsur)
    (hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖ ∂jetHaar) ≤ Eerror)
    (hε : 0 ≤ ε) (htrunc : ∀ z, ‖ideal z - model z‖ ≤ ε) :
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r)
    let D := allocatedPhysicalCubeDirections B U b S x (wholeReference r)
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let _V₁ := referenceJetEnvelopeWidths (q := dim) q H
    let _A := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ)
    let C := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight q cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    (∀ t, 1 ≤ H t) →
    C * (volumeFactor * (Eerror + 2 * δsur + (2 * η + εsample)) + ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * ε) ≤ δ →
    κ - δ ≤
      (∑ t : cells × window, (selectedResidueCellWeight q cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
          t.1.val t.2.val))).re := by
  intro root D H T V V₁ A C volumeFactor hV hZ hrowsize hprofile hH1 hcost
  apply allocatedRecenteredSelectedMean_l1_source B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells point test law r hlabel hwhole profile ideal model
    hq hN hτ hbudget hmesh hperiod htest hsource hε htrunc hV hZ hrowsize hprofile hH1 ?_ hcost
  intro a
  let target := columnResiduePattern q (standardPhysicalCubeFrame
    (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative q a.val)))
  have hwidth (z : Option (Fin dim) × X) : τ * (N z.2 : ℝ) ≤ V₁ z := by
    change τ * (N z.2 : ℝ) ≤ referenceJetEnvelopeWidths q (trimmedSpatialRootScale τ N q) z
    rw [referenceJetEnvelopeWidths_trimmed q N hq τ z]
    nlinarith [mul_pos hτ (Nat.cast_pos.mpr (hN z.2))]
  have hV₁ (z : Option (Fin dim) × X) : 0 < V₁ z := by
    exact (mul_pos hτ (Nat.cast_pos.mpr (hN z.2))).trans_le (hwidth z)
  have hsample := (Classical.choose_spec (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim)).2
    (I := X) (J := J) (O := O)
  obtain ⟨hZa, he⟩ := hsample rows hinj hcard hP hX hframe U μ ν base poly hp hm cover hcover hcoverP
    q hq hS₀ hS₀P hτ hεsample hτP hεsampleP hstride (fun i => (N i : ℝ)) hsize hrank hRrank
    {target} (Finset.singleton_nonempty _) V₁ hV₁ hwidth f g Lf Lg Cf Cg hf hg hfb hgb
    hη hamb hLf hLg hCf hCg hjet hηP ideal hi happrox hmass
  refine ⟨hZa, ?_⟩
  simpa only [hactual] using he

include hinj hcard hp μ in
theorem allocatedRecenteredSelectedMean_rank_l1_source_exp
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (ideal model : EuclideanJetLayers U O → ℂ)
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ ε : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfb : ∀ z, ‖f z‖ ≤ Cf) (hgb : ∀ z, ‖g z‖ ≤ Cg)
    (hactual : ∀ y, law.complexMean (fun a => profile a y) = f (coveredJetAmbientTorus U 1 y))
    (hi : Measurable ideal) {P Rrank S₀ η εsample δsur Eerror : ℝ}
    (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp P)
    (hS₀ : 0 ≤ S₀) (hS₀P : S₀ ≤ Real.exp P) (hstride : ∀ i, (q i : ℝ) ≤ S₀)
    (hτP : 1 / τ ≤ Real.exp P) (hεsample : 0 < εsample) (hεsampleP : 1 / εsample ≤ Real.exp P)
    (hsize : ∀ i, Real.exp ((P + (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ^ (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((P + (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ^ (Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,uO} m dim))) ≤ Rrank)
    (hη : 0 < η) (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hLf : (Lf : ℝ) ≤ Real.exp P) (hLg : (Lg : ℝ) ≤ Real.exp P)
    (hCf : (Cf : ℝ) ≤ Real.exp P) (hCg : (Cg : ℝ) ≤ Real.exp P)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P)
    (happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δsur)
    (hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖ ∂jetHaar) ≤ Eerror)
    (hε : 0 ≤ ε) (htrunc : ∀ z, ‖ideal z - model z‖ ≤ ε)
    {Pgeom Dgeom target : ℝ} (hPgeom : 0 ≤ Pgeom)
    (hMP : (M : ℝ) ≤ Real.exp Pgeom)
    (hperiodP : (modulus : ℝ) ≤ Real.exp (Pgeom ^ 2))
    (hdimP : ((dim + 1 : ℕ) : ℝ) ≤ Pgeom) (hGP : (Fintype.card G : ℝ) ≤ Pgeom)
    (hXP : (Fintype.card X : ℝ) ≤ Pgeom)
    (hDP : Dgeom ≤ Real.exp Pgeom) (hWL : W ≤ Dgeom * S.value)
    (hEaccuracy : Eerror ≤ l1SourceAccuracy target (coefficientErrorSpatialLog Pgeom) 0)
    (hδaccuracy : δsur ≤ l1SourceAccuracy target (coefficientErrorSpatialLog Pgeom) 0)
    (hηaccuracy : η ≤ l1SourceAccuracy target (coefficientErrorSpatialLog Pgeom) 0)
    (hsampleAccuracy : εsample ≤ l1SourceAccuracy target (coefficientErrorSpatialLog Pgeom) 0)
    (htruncAccuracy : ε ≤ l1SourceAccuracy target (coefficientErrorSpatialLog Pgeom) 0) :
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r)
    let D := allocatedPhysicalCubeDirections B U b S x (wholeReference r)
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let _V₁ := referenceJetEnvelopeWidths (q := dim) q H
    let _A := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ)
    let _C := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let _volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight q cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    (∀ t, 1 ≤ H t) →
    κ - Real.exp (-target) ≤
      (∑ t : cells × window, (selectedResidueCellWeight q cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
          t.1.val t.2.val))).re := by
  intro root D H T V V₁ A C volumeFactor hV hZ hrowsize hprofile hH1
  apply allocatedRecenteredSelectedMean_rank_l1_source B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells rows hinj hcard cover poly hp hm test μ ν
    law r hlabel hwhole profile ideal model hq hN hτ hbudget hmesh hperiod htest hsource
    f g Lf Lg Cf Cg hf hg hfb hgb hactual hi hP hX hframe hcover hcoverP
    hS₀ hS₀P hstride hτP hεsample hεsampleP hsize hrank hRrank hη hamb hLf hLg hCf hCg
    hjet hηP happrox hmass hε htrunc hV hZ hrowsize hprofile hH1
  exact physicalL1Source_error_le_exp dim X selection hPgeom hM hMP hperiodP hdimP hGP hXP
    (Nat.one_le_cast.mpr S.positive) hW hDP hWL
    hEaccuracy hδaccuracy hηaccuracy hsampleAccuracy htruncAccuracy

end Erdos3.VectorPolynomial

end

end OAI
