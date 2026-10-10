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

theorem allocatedRecenteredSelectedMean_square_perturbation
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (model : EuclideanJetLayers U O → ℂ) {κ Wmass Eerror δ : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (hδ : 0 ≤ δ) (hcost : Wmass * Eerror ≤ δ ^ 2) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
    let coeff := fun t : cells × window => (selectedResidueCellWeight q cells V t.1 : ℂ) *
      allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
        N hW mesh base cells test r t.1 t.2.val
    (∑ t, ‖coeff t‖) ≤ Wmass →
    (∑ t, ‖coeff t‖ * ‖law.complexMean (fun y => profile y (point (reconstruct t.1.val t.2.val))) -
      model (point (reconstruct t.1.val t.2.val))‖ ^ 2) ≤ Eerror →
    κ - δ ≤ (∑ t, coeff t * model (point (reconstruct t.1.val t.2.val))).re := by
  intro V reconstruct coeff hmass herror
  have hid := allocatedRecenteredProfileTerm_selected_mean (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test
    law r hlabel hwhole profile
  have he : law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) =
      ∑ t, coeff t * law.complexMean (fun y => profile y (point (reconstruct t.1.val t.2.val))) := by
    rw [hid, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, ← Finset.sum_coe_sort window]
    apply Finset.sum_congr rfl
    intro v _
    exact (mul_assoc _ _ _).symm
  rw [he] at hsource
  exact finiteSource_real_le_of_square_perturbation coeff _ _ hsource hmass herror hδ hcost

end Erdos3.VectorPolynomial

end

end OAI
