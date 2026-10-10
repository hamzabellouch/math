import OAI.Analysis.MetricEntropy.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

namespace OAI

universe uι uκ

/-!
# Relabelling finite real coordinates

The coordinate map is a linear homeomorphism of the full ambient spaces.
It transports all translation centers, rather than restricting them to the
body being covered. Consequently equality of covering numbers follows from
equality of the sets of admissible natural cover counts.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {κ : Type uκ}

/-- Relabel coordinates using `e`; no coordinate is removed or adjoined. -/
def coordinateEquiv (e : ι ≃ κ) : (ι → ℝ) ≃L[ℝ] (κ → ℝ) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply (e.symm j)
  continuous_invFun := continuous_pi fun i => continuous_apply (e i)

@[simp] theorem coordinateEquiv_apply (e : ι ≃ κ) (x : ι → ℝ) (j : κ) :
    coordinateEquiv e x j = x (e.symm j) := rfl

@[simp] theorem coordinateEquiv_symm_apply (e : ι ≃ κ) (y : κ → ℝ) (i : ι) :
    (coordinateEquiv e).symm y i = y (e i) := rfl

@[simp] theorem coordinateEquiv_symm (e : ι ≃ κ) :
    (coordinateEquiv e).symm = coordinateEquiv e.symm := by
  ext y i
  rfl

theorem coordinate_image_smul (e : ι ≃ κ) (r : ℝ) (A : Set (ι → ℝ)) :
    coordinateEquiv e '' (r • A) = r • (coordinateEquiv e '' A) :=
  Set.image_smul_comm (coordinateEquiv e) r A ((coordinateEquiv e).map_smul r)

theorem coordinate_isCompact_image (e : ι ≃ κ) (A : Set (ι → ℝ)) :
    IsCompact (coordinateEquiv e '' A) ↔ IsCompact A :=
  (coordinateEquiv e).toHomeomorph.isCompact_image

theorem coordinate_convex_image (e : ι ≃ κ) (A : Set (ι → ℝ)) :
    Convex ℝ (coordinateEquiv e '' A) ↔ Convex ℝ A := by
  constructor
  · intro h
    have hi := h.linear_image (coordinateEquiv e).symm.toLinearEquiv.toLinearMap
    change Convex ℝ ((coordinateEquiv e).symm '' (coordinateEquiv e '' A)) at hi
    simpa only [ContinuousLinearEquiv.symm_image_image] using hi
  · intro h
    exact h.linear_image (coordinateEquiv e).toLinearEquiv.toLinearMap

/-- This is interior in the full ambient function space. -/
theorem coordinate_interior_nonempty (e : ι ≃ κ) (A : Set (ι → ℝ)) :
    (interior (coordinateEquiv e '' A)).Nonempty ↔ (interior A).Nonempty := by
  have hi : coordinateEquiv e '' interior A = interior (coordinateEquiv e '' A) :=
    (coordinateEquiv e).toHomeomorph.image_interior A
  rw [← hi]
  exact Set.image_nonempty

@[simp] theorem mem_coordinate_image_iff (e : ι ≃ κ)
    (A : Set (RealSpace ι)) (y : RealSpace κ) :
    y ∈ coordinateEquiv e '' A ↔ (coordinateEquiv e).symm y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  · intro hy
    exact ⟨(coordinateEquiv e).symm y, hy,
      (coordinateEquiv e).apply_symm_apply y⟩

/-- Arbitrary ambient center lists are carried to arbitrary ambient center
lists. No requirement that centers belong to either covered set is added. -/
theorem covers_coordinate_image (e : ι ≃ κ) {M : ℕ}
    (A B : Set (RealSpace ι)) (c : Fin M → RealSpace ι) :
    Covers (coordinateEquiv e '' A) (coordinateEquiv e '' B)
      (fun j => coordinateEquiv e (c j)) ↔ Covers A B c := by
  constructor
  · intro h x hx
    obtain ⟨j, hj⟩ := h (coordinateEquiv e x) ⟨x, hx, rfl⟩
    refine ⟨j, ?_⟩
    have hh := (mem_coordinate_image_iff e B _).mp hj
    simpa only [map_sub, ContinuousLinearEquiv.symm_apply_apply] using hh
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨j, hj⟩ := h x hx
    exact ⟨j, x - c j, hj, map_sub (coordinateEquiv e) x (c j)⟩

theorem exists_cover_coordinate_image (e : ι ≃ κ) (M : ℕ)
    (A B : Set (RealSpace ι)) :
    (∃ c : Fin M → RealSpace κ,
      Covers (coordinateEquiv e '' A) (coordinateEquiv e '' B) c) ↔
      ∃ c : Fin M → RealSpace ι, Covers A B c := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j => (coordinateEquiv e).symm (c j), ?_⟩
    apply (covers_coordinate_image e A B _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc
  · rintro ⟨c, hc⟩
    exact ⟨fun j => coordinateEquiv e (c j),
      (covers_coordinate_image e A B c).mpr hc⟩

theorem coordinate_cover_counts (e : ι ≃ κ) (A B : Set (RealSpace ι)) :
    {M : ℕ | ∃ c : Fin M → RealSpace κ,
      Covers (coordinateEquiv e '' A) (coordinateEquiv e '' B) c} =
      {M : ℕ | ∃ c : Fin M → RealSpace ι, Covers A B c} := by
  ext M
  exact exists_cover_coordinate_image e M A B

theorem coverable_coordinate_image (e : ι ≃ κ) (A B : Set (RealSpace ι)) :
    Coverable (coordinateEquiv e '' A) (coordinateEquiv e '' B) ↔ Coverable A B := by
  unfold Coverable
  exact exists_congr fun M => exists_cover_coordinate_image e M A B

/-- Equality holds even before existence of a finite cover is established:
the two defining sets of natural counts are literally equal. -/
theorem coveringNumber_coordinate_image (e : ι ≃ κ) (A B : Set (RealSpace ι)) :
    coveringNumber (coordinateEquiv e '' A) (coordinateEquiv e '' B) =
      coveringNumber A B := by
  unfold coveringNumber
  rw [coordinate_cover_counts]

theorem coordinate_cube (e : ι ≃ κ) :
    coordinateEquiv e '' cube ι = cube κ := by
  ext y
  rw [mem_coordinate_image_iff]
  change (∀ i, |y (e i)| ≤ 1) ↔ ∀ j, |y j| ≤ 1
  constructor
  · intro h j
    simpa only [e.apply_symm_apply] using h (e.symm j)
  · intro h i
    exact h (e i)

section FiniteCoordinates

variable [Fintype ι] [Fintype κ]

theorem pairing_coordinateEquiv (e : ι ≃ κ) (x y : RealSpace ι) :
    pairing (coordinateEquiv e x) (coordinateEquiv e y) = pairing x y := by
  unfold pairing
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem l1Norm_coordinateEquiv (e : ι ≃ κ) (x : RealSpace ι) :
    l1Norm (coordinateEquiv e x) = l1Norm x := by
  unfold l1Norm
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem coordinate_l1Ball (e : ι ≃ κ) :
    coordinateEquiv e '' l1Ball ι = l1Ball κ := by
  ext y
  rw [mem_coordinate_image_iff]
  change l1Norm ((coordinateEquiv e).symm y) ≤ 1 ↔ l1Norm y ≤ 1
  rw [coordinateEquiv_symm, l1Norm_coordinateEquiv]

/-- Coordinate permutations preserve the literal pairing polar, with both
the body and its dual coordinates transported by the same map. -/
theorem coordinate_polar (e : ι ≃ κ) (K : Set (RealSpace ι)) :
    coordinateEquiv e '' polar K = polar (coordinateEquiv e '' K) := by
  ext y
  rw [mem_coordinate_image_iff]
  constructor
  · intro hy z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hp := pairing_coordinateEquiv e x ((coordinateEquiv e).symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hp
    rw [hp]
    exact hy x hx
  · intro hy x hx
    have hh := hy (coordinateEquiv e x) ⟨x, hx, rfl⟩
    have hp := pairing_coordinateEquiv e x ((coordinateEquiv e).symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hp
    rwa [hp] at hh

theorem IsSymmetricConvexBody.coordinate_image {K : Set (RealSpace ι)}
    (hK : IsSymmetricConvexBody K) (e : ι ≃ κ) :
    IsSymmetricConvexBody (coordinateEquiv e '' K) where
  isCompact := (coordinate_isCompact_image e K).mpr hK.isCompact
  convex := (coordinate_convex_image e K).mpr hK.convex
  symmetric y := by
    rw [mem_coordinate_image_iff, mem_coordinate_image_iff, map_neg]
    exact hK.symmetric ((coordinateEquiv e).symm y)
  interior_nonempty := (coordinate_interior_nonempty e K).mpr hK.interior_nonempty

theorem coordinate_body_iff (e : ι ≃ κ) (K : Set (RealSpace ι)) :
    IsSymmetricConvexBody (coordinateEquiv e '' K) ↔ IsSymmetricConvexBody K := by
  constructor
  · intro h
    have hh := h.coordinate_image e.symm
    simpa only [← coordinateEquiv_symm, ContinuousLinearEquiv.symm_image_image] using hh
  · exact fun h => h.coordinate_image e

/-- The exact dual covering number in the final theorem is unchanged, for
every scalar, with no convexity or covering premise needed for transport. -/
theorem coveringNumber_polar_cube_coordinate_image (e : ι ≃ κ)
    (K : Set (RealSpace ι)) (a : ℝ) :
    coveringNumber (polar (cube κ)) (a • polar (coordinateEquiv e '' K)) =
      coveringNumber (polar (cube ι)) (a • polar K) := by
  have h := coveringNumber_coordinate_image e (polar (cube ι)) (a • polar K)
  rw [coordinate_polar, coordinate_cube, coordinate_image_smul, coordinate_polar] at h
  exact h

end FiniteCoordinates

/-- The terminal ambient-space identification is a genuine linear
homeomorphism, not a cardinality-only relabelling. -/
def coordinatesToFin [Fintype ι] : (ι → ℝ) ≃L[ℝ] (Fin (Fintype.card ι) → ℝ) :=
  coordinateEquiv (Fintype.equivFin ι)

theorem coordinate_dimension_pos [Fintype ι] [Nonempty ι] : 0 < Fintype.card ι :=
  Fintype.card_pos

theorem coordinatesToFin_cube [Fintype ι] :
    coordinatesToFin (ι := ι) '' cube ι = cube (Fin (Fintype.card ι)) :=
  coordinate_cube (Fintype.equivFin ι)

theorem coordinatesToFin_body_iff [Fintype ι] (K : Set (RealSpace ι)) :
    IsSymmetricConvexBody (coordinatesToFin (ι := ι) '' K) ↔
      IsSymmetricConvexBody K :=
  coordinate_body_iff (Fintype.equivFin ι) K

theorem coordinatesToFin_coveringNumber_cube [Fintype ι] (K : Set (RealSpace ι)) :
    coveringNumber (coordinatesToFin (ι := ι) '' K) (cube (Fin (Fintype.card ι))) =
      coveringNumber K (cube ι) := by
  have h := coveringNumber_coordinate_image (Fintype.equivFin ι) K (cube ι)
  rw [coordinate_cube] at h
  exact h

theorem coordinatesToFin_coveringNumber_polar_cube [Fintype ι]
    (K : Set (RealSpace ι)) (a : ℝ) :
    coveringNumber (polar (cube (Fin (Fintype.card ι))))
      (a • polar (coordinatesToFin (ι := ι) '' K)) =
      coveringNumber (polar (cube ι)) (a • polar K) :=
  coveringNumber_polar_cube_coordinate_image (Fintype.equivFin ι) K a

/-- A positive ordinary dimension and the exact geometric and covering
identities for the coordinate equivalence `ℝ^Y ≃ ℝ^n`. Every body is
transported by one explicit ambient linear homeomorphism. -/
theorem finite_coordinate_realization [Fintype ι] [Nonempty ι] :
    ∃ n : ℕ, 0 < n ∧ ∃ E : RealSpace ι ≃L[ℝ] RealSpace (Fin n),
      E '' cube ι = cube (Fin n) ∧
      (∀ K : Set (RealSpace ι),
        IsSymmetricConvexBody (E '' K) ↔ IsSymmetricConvexBody K) ∧
      (∀ K : Set (RealSpace ι),
        coveringNumber (E '' K) (cube (Fin n)) = coveringNumber K (cube ι)) ∧
      (∀ (K : Set (RealSpace ι)) (a : ℝ),
        coveringNumber (polar (cube (Fin n))) (a • polar (E '' K)) =
          coveringNumber (polar (cube ι)) (a • polar K)) := by
  refine ⟨Fintype.card ι, coordinate_dimension_pos, coordinatesToFin,
    coordinatesToFin_cube, ?_, ?_, ?_⟩
  · exact coordinatesToFin_body_iff
  · exact coordinatesToFin_coveringNumber_cube
  · exact coordinatesToFin_coveringNumber_polar_cube

end MetricEntropyDuality

end

end OAI
