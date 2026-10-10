import OAI.Geometry.ProjectionVolume.ProductPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

def exposedFace {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : Set (Euclidean n) :=
  (innerSL ℝ u).toExposed K

@[simp] theorem exposedFace_zero {n : ℕ} (K : Set (Euclidean n)) : exposedFace K 0 = K := by
  ext x
  simp [exposedFace, ContinuousLinearMap.toExposed]

theorem exposedFace_nonempty {n : ℕ} (K : Set (Euclidean n)) (hK : IsCompact K)
    (hne : K.Nonempty) (u : Euclidean n) : (exposedFace K u).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (innerSL ℝ u).continuous.continuousOn
  exact ⟨x, hx, hmax⟩

theorem exposedFace_product {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (w : Euclidean (r + s)) :
    exposedFace (cartesianBody A B) w =
      cartesianBody (exposedFace A (splitEuclideanProduct r s w).1)
        (exposedFace B (splitEuclideanProduct r s w).2) := by
  ext x
  change (x ∈ cartesianBody A B ∧ ∀ y ∈ cartesianBody A B, ⟪w, y⟫ ≤ ⟪w, x⟫) ↔
    (((splitEuclideanProduct r s x).1 ∈ A ∧
      ∀ a ∈ A, ⟪(splitEuclideanProduct r s w).1, a⟫ ≤
        ⟪(splitEuclideanProduct r s w).1, (splitEuclideanProduct r s x).1⟫) ∧
    ((splitEuclideanProduct r s x).2 ∈ B ∧
      ∀ b ∈ B, ⟪(splitEuclideanProduct r s w).2, b⟫ ≤
        ⟪(splitEuclideanProduct r s w).2, (splitEuclideanProduct r s x).2⟫))
  constructor
  · rintro ⟨⟨hA, hB⟩, hmax⟩
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro a ha
      have hm : (splitEuclideanProduct r s).symm (a, (splitEuclideanProduct r s x).2) ∈
          cartesianBody A B := by
        rw [cartesianBody_eq_preimage, Set.mem_preimage,
          ContinuousLinearEquiv.apply_symm_apply]
        exact ⟨ha, hB⟩
      have h := hmax _ hm
      rw [splitEuclideanProduct_inner r s, splitEuclideanProduct_inner r s,
        ContinuousLinearEquiv.apply_symm_apply] at h
      exact (add_le_add_iff_right _).mp h
    · intro b hb
      have hm : (splitEuclideanProduct r s).symm ((splitEuclideanProduct r s x).1, b) ∈
          cartesianBody A B := by
        rw [cartesianBody_eq_preimage, Set.mem_preimage,
          ContinuousLinearEquiv.apply_symm_apply]
        exact ⟨hA, hb⟩
      have h := hmax _ hm
      rw [splitEuclideanProduct_inner r s, splitEuclideanProduct_inner r s,
        ContinuousLinearEquiv.apply_symm_apply] at h
      exact (add_le_add_iff_left _).mp h
  · rintro ⟨⟨hA, hmaxA⟩, ⟨hB, hmaxB⟩⟩
    refine ⟨⟨hA, hB⟩, ?_⟩
    intro y hy
    rw [splitEuclideanProduct_inner r s, splitEuclideanProduct_inner r s]
    exact add_le_add (hmaxA _ hy.1) (hmaxB _ hy.2)

theorem cartesianBody_eq_image {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    cartesianBody A B = (splitEuclideanProduct r s).symm '' (A ×ˢ B) := by
  ext x
  constructor
  · intro hx
    exact ⟨splitEuclideanProduct r s x, hx, (splitEuclideanProduct r s).symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change splitEuclideanProduct r s ((splitEuclideanProduct r s).symm y) ∈ A ×ˢ B
    simpa using hy

theorem submodule_prod_finrank {r s : ℕ} (P : Submodule ℝ (Euclidean r))
    (Q : Submodule ℝ (Euclidean s)) :
    Module.finrank ℝ (P.prod Q) = Module.finrank ℝ P + Module.finrank ℝ Q := by
  let e : (P.prod Q) ≃ₗ[ℝ] P × Q :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun x => ⟨(x.1, x.2), ⟨x.1.2, x.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod]

theorem cartesianBody_affine_dimension {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    Module.finrank ℝ (vectorSpan ℝ (cartesianBody A B)) =
      Module.finrank ℝ (vectorSpan ℝ A) + Module.finrank ℝ (vectorSpan ℝ B) := by
  let e := (splitEuclideanProduct r s).symm.toLinearEquiv
  rw [cartesianBody_eq_image]
  change Module.finrank ℝ (vectorSpan ℝ (e.toLinearMap.toAffineMap '' (A ×ˢ B))) = _
  rw [← AffineMap.map_vectorSpan]
  change Module.finrank ℝ ((vectorSpan ℝ (A ×ˢ B)).map e.toLinearMap) = _
  rw [e.finrank_map_eq, vectorSpan_prod_eq hA hB, submodule_prod_finrank]

end Paper092

end

end OAI
