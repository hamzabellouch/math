import OAI.Combinatorics.Progressions.Estimates.AllocatedCutoffReferenceEnvelope
import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
variable (r : ℝ≥0) (hr : 0 < r) (hR₀ : ∀ j, 0 < R₀ j) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

variable (rowSets : Fin m → Finset (Finset (Fin dim)))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

variable (hbudgetRows : ∀ j, ((rowSets j).card + 1 : ℝ) *
  (Fintype.card (Finset (Fin dim)) * (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (r : ℝ) * R₀ j)))) ≤ 1 / 4)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (κ : ℝ≥0) (hκ : ∀ j, (R₀ j)⁻¹ ≤ κ)

local notation "kernelLip" => (ampN * (Fintype.card (Finset (Fin dim)) *
  (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
    (κ * ∑ j, D j * Fintype.card (J j))) * ∑ j, (Finset.card (rowSets j) : ℝ≥0))))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets r *
  (2 * ((2 : ℝ) ^ dim * (2 * (r : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

include hR₀ hσ1 hC hchart hbudgetRows hb bW hD hκ in
theorem allocatedNormalizedCutoff_sampled_recentered_mass {K : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K rowTypes rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ (N x : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L)
    (hamb : (Fintype.card (JetAmbientIndex rowTypes J) : ℝ) ≤ L)
    (hηL : η⁻¹ ≤ Real.exp L) (hLip : (kernelLip : ℝ) ≤ Real.exp L)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * amp ≤ Real.exp P)
    (base : X → ℤ) (modulus : ℕ)
    (wholeReference :
      (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Wsp ξ : ℝ} (hWsp : 0 ≤ Wsp) (hξ : 0 < ξ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) Wsp ρ ξ N) z)
    (hrows : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ trimmedSpatialRootScale ρ N stride t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale ρ N stride t) :
    let spatialFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + Wsp) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let point := physicalCubeRowSample U d rows p hm
    let cutoff := allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
    law.mean (allocatedRecenteredProfileMass (W := Wsp) (τ := ρ) (ξ := ξ) B U b S X modulus stride
      wholeReference x N base cells point (fun _ y => ((amp * ‖cutoff y‖ : ℝ) : ℂ))) ≤
        spatialFactor * (massCap + 2 * η + ε) ∧
    ∀ (qKernel : ℕ) (δ : ℝ≥0)
      (Q : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        EuclideanJetLayers U rowTypes → ℂ) {A θ : ℝ}, 0 ≤ A → 0 ≤ θ →
      (∀ y₀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW qKernel y₀
        (allocatedPhysicalLongIdeal B U b hR₀ S rowSets δ) y - Q y₀ y‖ ≤ amp * A * (‖cutoff y‖ * θ)) →
      law.mean (allocatedRecenteredProfileMass (W := Wsp) (τ := ρ) (ξ := ξ) B U b S X modulus stride
        wholeReference x N base cells point
        (fun y₀ y => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW qKernel y₀
          (allocatedPhysicalLongIdeal B U b hR₀ S rowSets δ) y - Q y₀ y)) ≤
            (A * θ) * (spatialFactor * (massCap + 2 * η + ε)) := by
  intro spatialFactor law point cutoff
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
  have href (cell : ColumnResiduePattern (Option (Fin dim)) X stride) :
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {cell}
        (referenceJetEnvelopeWidths (q := dim) stride (trimmedSpatialRootScale ρ N stride)) z,
        selectedResidueDensityMass stride {cell}
          (referenceJetEnvelopeWidths (q := dim) stride (trimmedSpatialRootScale ρ N stride))
          (fun z => amp * ‖cutoff (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤
            massCap + 2 * η + ε :=
    allocatedNormalizedCutoff_reference_envelope (X := X) (J := J) B U b o S r hr hR₀ hσ1 C hC hchart
      rowSets hbudgetRows hb bW D hD κ hκ hSampling hP hn hdim μ ν p hp hm d stride hs
      hS hSP hρ hε hρP hεP hstride N hsize hrank hR hη hL hamb hηL hLip hfreqP hcoeffP base cell
  constructor
  · exact allocatedNormalizedCutoff_recentered_mass B U b S rowSets o hb bW d r hr p hm
      stride N hs hN modulus wholeReference x base hWsp hρ hξ cells hZ hrows hscale href
  · intro qKernel δ Q A θ hA hθ herr
    exact allocatedProductIdealError_recentered_mass B U b S rowSets o hb bW d r hr p hm
      stride N hs hN modulus wholeReference x base hWsp hρ hR₀ qKernel δ Q
      hA hθ hξ cells hZ hrows hscale href herr

end Erdos3.BooleanCubeKernel

end

end OAI
