import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests
import OAI.Combinatorics.Progressions.Lattices.AllocatedPointwiseResidueCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedResidueSiteWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredIdealCover_expansion
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (htest : ∀ s u, ‖test s u‖ ≤ 1)
    (hg : ∀ k s u, ‖g r k s u‖ ≤ 1) :
    let factor := fun (t : terms) (k : ∀ j, ((coverWitness r).expansion j).Term)
        (s : Finset (Fin dim)) (u : X → ℤ) =>
      test s (fun z => (u z : ℝ)) * twist r.val a.val t s u *
        g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) /
          commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))
    (∀ t k s u, ‖factor t k s u‖ ≤ 1) ∧
    ∀ v : X → (Unit ⊕ Fin dim) → ℤ,
      allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
        allocatedSupportedIdealCoverValue B U b hR hσ S refined coverWitness hb o bW d g δ x p hm
          (point v) r.val =
      ∑ t : terms, ∑ k : ∀ j, ((coverWitness r).expansion j).Term,
        ((coeff (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)) *
          coverSiteCoefficient (coverWitness r).expansion k) *
        (allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x refined
            (coverWitness r).representative (coverWitness r).positive hb o bW
            (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
            (physicalCubeRowSample U d rows p hm (point v)) *
          ∏ s, factor t k s (physicalCubeVertexValue (point v) s)) := by
  dsimp only
  constructor
  · intro t k s u
    rw [norm_mul, norm_mul]
    have ht := allocatedRecenteredSpatialTwist_bound (τ := τ) B U b S X modulus q wholeReference x N mesh base
      hmesh r.val a.val t s u
    exact (mul_le_mul (mul_le_mul (htest s _) ht (norm_nonneg _) zero_le_one)
      (hg k s _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
  · intro v
    rw [allocatedRecenteredResidueWeight_expansion B U b S X modulus q wholeReference x N mesh base
      hM selection hx hW cells hq]
    simp only [allocatedSupportedIdealCoverValue, dite_eq_left r.property]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.prod_mul_distrib]
    ring

end Erdos3.VectorPolynomial

end

end OAI
