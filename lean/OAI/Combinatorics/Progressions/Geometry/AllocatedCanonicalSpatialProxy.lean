import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceWindowTest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def anisotropicVectorSiteError {α G : Type*} [Fintype α] [Fintype G]
    (X N : Type*) [Fintype X] [Fintype N] (selection : α ↪ G)
    (M modulus : ℕ) (W κ C₀ ρ ξ r : ℝ) : ℝ :=
  let E := anisotropicSpatialError selection N M κ C₀ ρ ξ
  let Γ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
  Fintype.card X * (E + 4 * Γ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
    (1 + Γ * anisotropicSpatialDensityCap selection κ + E) ^ Fintype.card X

theorem anisotropicVectorSiteError_nonneg {α G : Type*} [Fintype α] [Fintype G]
    (X N : Type*) [Fintype X] [Fintype N] (selection : α ↪ G) (M modulus : ℕ)
    {W κ C₀ ρ ξ r : ℝ} (hW : 0 ≤ W) (hκ : 0 ≤ κ) (hC : 0 ≤ C₀)
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) (hr : 0 ≤ r) :
    0 ≤ anisotropicVectorSiteError X N selection M modulus W κ C₀ ρ ξ r := by
  have he := anisotropicSpatialError_nonneg selection N M hκ hC hρ hξ
  have hc := anisotropicSpatialDensityCap_nonneg selection hκ
  have hl := anisotropicSpatialDensityLip_nonneg selection hκ
  unfold anisotropicVectorSiteError
  positivity

namespace VectorPolynomial

open BooleanCubeKernel
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))

noncomputable def allocatedCenteredSpatialLaw {X : Type*} [Fintype X]
    (Q : Option vars × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) : PMF (X → (Unit ⊕ α) → ℤ) :=
  (smoothProductPMF Q hQ).map (centeredPhysicalCubeMap
    (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w))
    (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w)))

noncomputable def allocatedCanonicalSpatialProxy {X : Type*} [Fintype X]
    (selection : α ↪ G) (hp : (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection).det ≠ 0)
    (H : X → ℝ) (W : ℝ) (hW : 0 ≤ W) (modulus : ℕ) [NeZero modulus]
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
    (mesh : ℝ) (v : X → (Unit ⊕ α) → ℤ) : ℂ :=
  ∏ d, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun j => c (Sum.inr j)) id
        (principalAxisResidueJoin grid u modulus label))))
    modulus (canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)) (H d) 3 mesh (v d)

omit [DecidableEq G] [DecidableEq α] in
theorem allocatedTrimmedSpatial_common_window {X : Type*} [Fintype X]
    (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    centeredPhysicalCubeWindow (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w))
      (residueProfileWidth q (trimmedSpatialWidths (K := vars) W τ N)) ⊆
        commonSpatialWindow (trimmedSpatialRootScale τ N q) := by
  intro v hv
  exact (mem_commonSpatialWindow_scaled_iff _
    (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1) v).mpr
      (allocatedTrimmedSpatial_window_bound B U basis S c x (principalAxisJoin grid u w)
        N q hN hq hW hτ hbudget v hv)

theorem allocatedTrimmedSpatial_fiber_site_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, ((|c (.inr j)| : ℤ) + (sides j : ℤ) : ℝ) ≤ ξ * (1 + W))
    (hprincipalDir : ∀ j, ((|c (.inr j)| : ℤ) + (sides j : ℤ) : ℝ) ≤ ξ * S.value)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
    (hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (hmesh : 0 < mesh)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
    (w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hw : principalResidueLabel modulus w = label)
    (v : X → (Unit ⊕ α) → ℤ) (hv : v ∈ commonSpatialWindow (trimmedSpatialRootScale τ N q)) :
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := trimmedSpatialWidths (K := vars) W τ N
    let hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ‖(((∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i) *
        (allocatedCenteredSpatialLaw B U basis S c x u Q hQ w v).toReal : ℝ) : ℂ) -
      allocatedCanonicalSpatialProxy B U basis S c x u selection hp H W hW modulus label mesh v‖ ≤
      anisotropicVectorSiteError X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
        M modulus W κ C₀ ρ ξ mesh := by
  intro H T V hV Q hQ hp
  have h := allocatedTrimmedSpatial_vector_site_error B U basis S c x (principalAxisJoin grid u w)
    selection N q hN hq hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ0 hξ1 hprincipalRoot hprincipalDir
    hsize hmeshSize modulus hperiod (by norm_num : (0 : ℝ) < 3) hmesh v
    ((mem_commonSpatialWindow_scaled_iff H
      (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1) v).mp hv)
  dsimp only [H, T, V, Q]
  unfold allocatedCenteredSpatialLaw centeredPhysicalCubeMap
  simpa only [allocatedCanonicalSpatialProxy,
    anisotropicVectorSiteError, principalSpatialColumns_join_residue, hw] using h

end VectorPolynomial
end Erdos3

end

end OAI
