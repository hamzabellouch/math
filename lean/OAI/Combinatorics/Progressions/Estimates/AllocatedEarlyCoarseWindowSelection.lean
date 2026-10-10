import OAI.Combinatorics.Progressions.Dynamics.AllocatedEarlyWindowSelectionBudget
import OAI.Combinatorics.Progressions.Probability.AllocatedEarlyCoverCoefficientMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (coverWitness : (r : (AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "terms" => allocatedResidueCoverTerms B U b S (residueRefinedPeriod modulus q) coverWitness
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "residue" => (fun (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) j =>
  integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict grid (AllocatedResidueSiteWitness.representative (coverWitness r))) rows j
    (principalAxisRestrict (fun a => ¬grid a) (AllocatedResidueSiteWitness.representative (coverWitness r))))
    (residueRefinedPeriod modulus q))

theorem allocatedEarlyCoarseWindow_selection
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    {Qcover : ℝ}
    (hcover : allocatedResidueCoverCoefficientMass B U b S (residueRefinedPeriod modulus q) coverWitness ≤
      Real.exp Qcover)
    {D pgeo Pmask e : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) O D)
    (hpgeo : 0 ≤ pgeo) (hPmask : 0 ≤ Pmask) (he : 0 ≤ e)
    (hRP : ∀ j, R j ≤ Real.exp pgeo) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pgeo)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      physicalIdealErrorShare 0 (allocatedIdealMeshEnvelope m D pgeo e))
    (hmask : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) j z,
      0 ≤ allocatedIntegerKernelMask B U b S x rows j (residueRefinedPeriod modulus q) (residue r j) z ∧
      allocatedIntegerKernelMask B U b S x rows j (residueRefinedPeriod modulus q) (residue r j) z ≤
        Real.exp (allocatedSiteKernelMaskLog m Pmask)) :
    let mesh : ℝ := allocatedEarlyRecenteredMesh X selection M modulus p E
    let costLog : ℝ := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p + E))
    let volume : ℝ := ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
    let a := fun (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (t : X → SpatialSiteLabel (Fin dim) modulus 4 mesh) =>
      allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
        (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)
    ∀ F : ∀ r, (X → SpatialSiteLabel (Fin dim) modulus 4 mesh) × terms r → EuclideanJetLayers U O → ℂ,
    (∀ r t, Measurable (F r t)) → (∀ r t y, ‖F r t y‖ ≤ 1) →
    ∀ η : ℝ, 0 < η →
    η ≤ ‖allocatedWindowCoverMixture B U b hR hσ S (residueRefinedPeriod modulus q) coverWitness
      hb o bW d x ν δ (fun _ => X → SpatialSiteLabel (Fin dim) modulus 4 mesh) a F‖ →
    ∃ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (t : X → SpatialSiteLabel (Fin dim) modulus 4 mesh) (k : terms r) (y : EuclideanJetLayers U O),
      a r t ≠ 0 ∧ coverSiteCoefficient (coverWitness r).expansion k ≠ 0 ∧
      allocatedResidueIdealWindowPrefactor B U b hR hσ S (residueRefinedPeriod modulus q) coverWitness
        hb o bW d x δ r y ≠ 0 ∧
      η * volume / (2 * Real.exp (allocatedSiteFamilyWindowLog D +
        D * allocatedSiteKernelMaskLog m Pmask + 1 + (costLog + Qcover))) ≤ ‖F r (t, k) y‖ ∧
      ∀ s : ℝ, 0 ≤ s → D ≤ allocatedComparisonDimension m s → p + E ≤ s → Pmask ≤ s → Qcover ≤ s →
        η * volume * Real.exp (-allocatedEarlyWindowSelectionLog m dim s) ≤ ‖F r (t, k) y‖ := by
  intro mesh costLog volume a F hF hFbound η hη hlower
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  have hcoeff := allocatedEarlyCoverCoefficient_mass B U b S X modulus q wholeReference coverWitness
    x hM selection hx N hW hp hE hG hX hMP hmod hq hN hτ hbudget hperiod hcover
  obtain ⟨r, t, k, y, ht, hk, hy, hgain⟩ :=
    allocatedIdealWindow_probability_volume_selection B U b hR hσ S (residueRefinedPeriod modulus q)
      coverWitness hb o bW d x ν hdim hpgeo hPmask he hRP hRi δ hδ hδ1 hδe hmesh hmask
      (fun _ => X → SpatialSiteLabel (Fin dim) modulus 4 mesh) a F hF hFbound hη hvolume hcoeff hlower
  refine ⟨r, t, k, y, ht, hk, hy, hgain, ?_⟩
  intro s hs hDs hps hPs hQs
  have hdenom := allocatedEarlyWindowSelection_denominator m dim hp hE hPmask hdim.nonneg hs hDs hps hPs hQs
  calc
    η * volume * Real.exp (-allocatedEarlyWindowSelectionLog m dim s) =
        η * volume / Real.exp (allocatedEarlyWindowSelectionLog m dim s) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    _ ≤ η * volume / (2 * Real.exp (allocatedSiteFamilyWindowLog D +
        D * allocatedSiteKernelMaskLog m Pmask + 1 + (costLog + Qcover))) :=
      div_le_div_of_nonneg_left (mul_nonneg hη.le hvolume.le) (by positivity) hdenom
    _ ≤ ‖F r (t, k) y‖ := hgain

end Erdos3.VectorPolynomial

end

end OAI
