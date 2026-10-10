import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealReferenceInsertion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRefinedProfileCoefficient_mass
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    (hH : ∀ t, 1 ≤ trimmedSpatialRootScale τ N q t)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ z, ‖test z‖ ≤ 1)
    (u : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
    (r : PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) :
    (∑ t : cells × spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells test u r t‖) ≤
      coefficientTailSpatialFactor X selection M modulus W S.value := by
  let H := trimmedSpatialRootScale τ N q
  let T := trimmedSpatialSlopeScale W τ N q
  let A : ℝ := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
  let C : ℝ := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
  let ψ := allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh u r
  have hA : 0 < A := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (lt_of_lt_of_le zero_lt_one (hH t))
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2 (Nat.cast_pos.mpr S.positive) i))
  have hC : 0 ≤ C := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (by positivity))) _
  have hψ : ∀ w ∈ spatialWindow (α := Fin dim) H 4, ‖ψ w‖ ≤ C :=
    allocatedReferenceSpatialProxy_bound B U b S x
      (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u (reference u r))
      hM selection hx modulus hperiod H (fun t => lt_of_lt_of_le zero_lt_one (hH t)) hW hbudget hmesh
  have hcard := spatialWindow_card_anisotropic (α := Fin dim) H T hH (by norm_num : (0 : ℝ) ≤ 4)
    (Nat.cast_ne_zero.mpr S.positive.ne') (trimmedSpatial_scale_ratio hW N q)
  norm_num only [show 2 * (4 : ℝ) + 1 = 9 by norm_num] at hcard
  have h := selectedResidue_coefficient_tail q cells _ (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
    (spatialWindow (α := Fin dim) H 4) ψ
    (fun a w => test (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r a w))
    (fun _ _ => (1 : ℝ)) hA hC zero_le_one hψ (fun _ _ => htest _) (fun _ _ => le_rfl) hcard
  simpa only [allocatedRefinedProfileCoefficient, coefficientTailSpatialFactor, mul_one] using h

end Erdos3.VectorPolynomial

end

end OAI
