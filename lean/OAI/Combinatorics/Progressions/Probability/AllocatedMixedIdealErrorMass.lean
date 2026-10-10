import OAI.Combinatorics.Progressions.Estimates.AllocatedCutoffCoveredEnvelope
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMeasurable
import OAI.Combinatorics.Progressions.Estimates.FiniteWeightedErrorIntegral

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
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

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))
local notation "envelope" => allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets r *
  (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

omit [NeZero period] in
include hR hC hchart hbudget in
theorem allocatedProductIdealError_integrable_integral_le
    (hσ1 : ∀ j, σ j ≤ 1) (δ : ℝ≥0)
    (P : EuclideanJetLayers U rowTypes → ℂ) (hP : Measurable P)
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (herr : ∀ y : EuclideanJetLayers U rowTypes,
      ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
          (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y‖ ≤
        ‖inverseNormalizer‖ * A * (‖cutoff y‖ * ε)) :
    Integrable (fun y => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y) haar ∧
    (∫ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y‖ ∂haar) ≤ (A * ε) * massCap := by
  let F := fun y => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y
  have hF (y : EuclideanJetLayers U rowTypes) : ‖F y‖ ≤ (A * ε) * envelope y := by
    calc
      ‖F y‖ ≤ ‖inverseNormalizer‖ * A * (‖cutoff y‖ * ε) := herr y
      _ = (A * ε) * (‖inverseNormalizer‖ * ‖cutoff y‖) := by ring
      _ ≤ (A * ε) * envelope y := mul_le_mul_of_nonneg_left
        (allocatedProductIdealNormalizer_cutoff_le_covered_envelope B U b S rowSets o hb bW d r hr
          hR C hC hchart hbudget y) (mul_nonneg hA hε)
  have hE := allocatedCutoffCoveredEnvelope_integrable B U b S rowSets o hb bW d r hR ν
  have hmF : Measurable F := (allocatedProductFullGridPrefactor_measurable B U b S rowSets d r hr x hb o bW q y₀
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
    (allocatedPhysicalLongIdeal_measurable B U b hR S rowSets δ)).sub hP
  have hiF : Integrable F haar := (hE.const_mul (A * ε)).mono' hmF.aestronglyMeasurable
    (Filter.Eventually.of_forall hF)
  have hmass : (∫ y, envelope y ∂haar) ≤ massCap := by
    have h := allocatedCutoffCoveredEnvelope_integral_abs_le B U b S rowSets o hb bW d r hR ν hσ1
    have h' : (∫ y, envelope y ∂haar) ≤ allocatedCutoffGridVolumeCap B U b S rowSets r *
        (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) := by
      simpa only [abs_of_nonneg (allocatedCutoffCoveredEnvelope_nonneg B U b S rowSets o hb bW d r hR _)] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (allocatedCutoffGridVolumeCap_le_uniform B U b S rowSets r)
      (by positivity))
  refine ⟨hiF, ?_⟩
  calc
    (∫ y, ‖F y‖ ∂haar) ≤ ∫ y, (A * ε) * envelope y ∂haar := integral_mono hiF.norm (hE.const_mul _) hF
    _ = (A * ε) * ∫ y, envelope y ∂haar := integral_const_mul _ _
    _ ≤ (A * ε) * massCap := mul_le_mul_of_nonneg_left hmass (mul_nonneg hA hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
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

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))
local notation "envelope" => allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets r *
  (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

local notation "principalTuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)

omit [NeZero period] in
include hR hC hchart hbudget in
theorem allocatedProductIdealError_probability_integral_le
    (hσ1 : ∀ j, σ j ≤ 1) (δ : ℝ≥0) (law : FiniteProbabilityWeights principalTuples)
    (P : principalTuples → EuclideanJetLayers U rowTypes → ℂ) (hP : ∀ z, Measurable (P z))
    (W : EuclideanJetLayers U rowTypes → principalTuples → ℂ)
    (hW : ∀ z, Measurable (fun y => W y z)) (hW1 : ∀ y z, ‖W y z‖ ≤ 1)
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (herr : ∀ z (y : EuclideanJetLayers U rowTypes),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q z
          (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P z y‖ ≤
        ‖inverseNormalizer‖ * A * (‖cutoff y‖ * ε)) :
    Integrable (fun y => law.complexMean (fun z => W y z *
      (allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q z
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P z y))) haar ∧
    (∫ y, ‖law.complexMean (fun z => W y z *
      (allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q z
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P z y))‖ ∂haar) ≤ (A * ε) * massCap := by
  let F := fun y z => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q z
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P z y
  have hd (z : principalTuples) : Integrable (fun y => F y z) haar ∧
      (∫ y, ‖F y z‖ ∂haar) ≤ (A * ε) * massCap :=
    allocatedProductIdealError_integrable_integral_le B U b S rowSets x z q d r hr hb o bW
      hR C hC hchart hbudget ν hσ1 δ (P z) (hP z) hA hε (herr z)
  have h := law.weighted_error_integral_le haar F W (fun z => (hd z).1) hW hW1
    (fun _ => (A * ε) * massCap) (fun z => (hd z).2)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3.VectorPolynomial

end

end OAI
