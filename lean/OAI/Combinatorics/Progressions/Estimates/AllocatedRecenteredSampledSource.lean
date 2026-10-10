import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
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
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem allocatedRecenteredSelectedMean_sampled_source
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (model : EuclideanJetLayers U O → ℂ)
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ Eerror : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (hδ : 0 ≤ δ) :
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r)
    let D := allocatedPhysicalCubeDirections B U b S x (wholeReference r)
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let V₁ := referenceJetEnvelopeWidths (q := dim) q H
    let _outputScale := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ)
    let C := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight q cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    (∀ t, 1 ≤ H t) →
    (∀ a : cells,
      let target := columnResiduePattern q (standardPhysicalCubeFrame
        (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative q a.val)))
      (0 < ∑' z, selectedResidueSmoothWeight q {target} V₁ z) ∧
      selectedResidueDensityMass q {target} V₁ (fun z =>
        ‖law.complexMean (fun y => profile y (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          model (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖ ^ 2) ≤ Eerror) →
    (C * ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X)) * (C * (volumeFactor * Eerror)) ≤ δ ^ 2 →
    κ - δ ≤
      (∑ t : cells × window, (selectedResidueCellWeight q cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
          t.1.val t.2.val))).re := by
  intro root D H T V V₁ A C volumeFactor hV hZ hrows hprofile hH1 he hcost
  have hH (t) : 0 < H t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  let ψ := allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh
    (principalResidueLabel modulus (wholeReference r))
  have hC : 0 ≤ C := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg _)))) _
  have hψ : ∀ v ∈ window, ‖ψ v‖ ≤ C :=
    allocatedResidueSpatialKernel_norm_le B U b S x X hM selection hx modulus H hW mesh
      hH hbudget hmesh hperiod (principalResidueLabel modulus (wholeReference r))
  have hid := allocatedRecenteredProfileTerm_selected_mean (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test
    law r hlabel hwhole profile
  have hsource' : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative q t.1.val) q t.2.val) *
        law.complexMean (fun y => profile y (point
          (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative q t.1.val) q t.2.val)))).re := by
    rw [hid] at hsource
    rw [Fintype.sum_prod_type]
    convert hsource using 1
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, ← Finset.sum_coe_sort window]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [allocatedRecenteredResidueWeight, allocatedWholeResidueReconstruction, ψ, A, root, D, H, T]
    ring
  have ht := physicalReconstruction_source_of_sampled_square_geometric q hq root D base cells V hV hZ H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q) hrows hprofile
    ψ test (fun w => law.complexMean (fun y => profile y (point w))) (fun w => model (point w))
    hC hψ htest he hsource' hδ hH1 hcost
  convert ht using 1
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  dsimp only [allocatedRecenteredResidueWeight, allocatedWholeResidueReconstruction, ψ, A, root, D, H, T]
  ring

end Erdos3.VectorPolynomial

end

end OAI
