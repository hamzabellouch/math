import OAI.CategoryTheory.Thomason.Gray.GraySingularPathComparison
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.SingularAcyclicFibers
import OAI.CategoryTheory.Thomason.Strict.StrictPosetWeakEquivalences

namespace OAI

section

/-! # Recovering positive faces from strict coordinate cuts

Every face with positive mass separates its inside vertices strictly from
its outside vertices. This is the uniqueness step for barycentric flags.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder

noncomputable section

private theorem comparable_face_weights (n : ℕ) (A B : Faces n)
    (h : A ≤ B ∨ B ≤ A) (i j : Fin (n+1))
    (hi : ULift.up i ∈ A.finset) (hj : ULift.up j ∉ A.finset) :
    (face n B).weights j ≤ (face n B).weights i := by
  classical
  rcases h with h | h
  · have hiB : ULift.up i ∈ B.finset := h hi
    rw [face_weight n B i, ite_eq_left hiB, face_weight n B j]
    split_ifs
    · exact le_rfl
    · positivity
  · have hjB : ULift.up j ∉ B.finset := fun hB => hj (h hB)
    rw [face_weight n B j, ite_eq_right hjB]
    exact (face n B).nonneg i

/-- A positively weighted face is a strict upper-level set of the resulting
geometric point. Ties can occur only within one side of its boundary. -/
theorem positive_face_strict_cut (n : ℕ)
    (z : SSet.toTop.obj (nerve (Faces n))) (A : Faces n)
    (hA : 0 < (PosetGeometry.coordinates (Faces n) z).weights A)
    (i j : Fin (n+1)) (hi : ULift.up i ∈ A.finset) (hj : ULift.up j ∉ A.finset) :
    (point n z).weights j < (point n z).weights i := by
  classical
  let := Fintype.ofFinite (Faces n)
  have hchain := PosetGeometry.coordinates_chainSupported z
  have hm (B : Faces n) :
      (PosetGeometry.coordinates (Faces n) z).weights B * (face n B).weights j ≤
        (PosetGeometry.coordinates (Faces n) z).weights B * (face n B).weights i := by
    by_cases hB : (PosetGeometry.coordinates (Faces n) z).weights B = 0
    · simp [hB]
    · apply mul_le_mul_of_nonneg_left _ ((PosetGeometry.coordinates (Faces n) z).nonneg B)
      apply comparable_face_weights n A B _ i j hi hj
      exact hchain A (Finsupp.mem_support_iff.mpr (ne_of_gt hA)) B
        (Finsupp.mem_support_iff.mpr hB)
  rw [point_weight, point_weight]
  apply Finset.sum_lt_sum (fun B _ => hm B)
  refine ⟨A, Finset.mem_univ A, ?_⟩
  apply mul_lt_mul_of_pos_left _ hA
  rw [face_weight n A j, ite_eq_right hj]
  exact (face_weight_pos_iff n A i).mpr hi

/-- After sorting the resulting coordinates, every positive face is an
initial segment of that same ordering. Thus the active faces share one flag. -/
theorem positive_face_sorted_lower (n : ℕ)
    (z : SSet.toTop.obj (nerve (Faces n))) (A : Faces n)
    (hA : 0 < (PosetGeometry.coordinates (Faces n) z).weights A)
    (σ : Equiv.Perm (Fin (n+1)))
    (hσ : Antitone (fun i => (point n z).weights (σ i))) :
    IsLowerSet {i : Fin (n+1) | ULift.up (σ i) ∈ A.finset} := by
  intro i j hij hj
  by_contra hi
  have hcut := positive_face_strict_cut n z A hA (σ i) (σ j) hj hi
  exact (not_lt_of_ge (hσ hij)) hcut

/-- A nonempty positive face is one full prefix of the sorted vertices,
with an actual last index. -/
theorem positive_face_sorted_prefix (n : ℕ)
    (z : SSet.toTop.obj (nerve (Faces n))) (A : Faces n)
    (hA : 0 < (PosetGeometry.coordinates (Faces n) z).weights A)
    (σ : Equiv.Perm (Fin (n+1)))
    (hσ : Antitone (fun i => (point n z).weights (σ i))) :
    ∃ k : Fin (n+1), ∀ i : Fin (n+1), ULift.up (σ i) ∈ A.finset ↔ i ≤ k := by
  classical
  let S := Finset.univ.filter (fun i : Fin (n+1) => ULift.up (σ i) ∈ A.finset)
  have hS : S.Nonempty := by
    obtain ⟨v, hv⟩ := A.nonempty
    refine ⟨σ.symm v.down, ?_⟩
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.apply_symm_apply, ULift.up_down] using hv
  refine ⟨S.max' hS, fun i => ?_⟩
  constructor
  · intro hi
    exact Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · intro hi
    exact positive_face_sorted_lower n z A hA σ hσ hi
      (Finset.mem_filter.mp (Finset.max'_mem S hS)).2

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The actual Street weak test through singular paths and homotopy fibres -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Singular internal-hom paths preserve and reflect the original actual
weak-equivalence test, for arbitrary continuous maps. -/
theorem singular_path_internalHom_weak_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    realizationWeakEquivalences ((ihom (Δ[1] : SSet.{0})).map (TopCat.toSSet.map p)) ↔
      IsWeakHomotopyEquivalence p.hom := by
  rw [← realizationWeakEquivalences.arrow_mk_iso_iff (singularPathMapArrowIso p)]
  exact (singular_map_weak_iff (continuousPathMap p)).trans (continuousPathMap_weak_iff p)

/-- Every actual homotopy fibre of a weak map is weakly contractible. The
mapping-path projection and its Kan property are constructed explicitly. -/
theorem weak_map_homotopy_fiber_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y) :
    IsWeakHomotopyEquivalence (ContinuousMap.const
      {z : mappingPathSpace p // (mappingPathProjection p).hom z = y} ()) := by
  let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map (mappingPathProjection p)) :=
    mappingPath_singular_fibration p
  exact singular_fibration_fiber_weak (mappingPathProjection p)
    ((mappingPathProjection_weak_iff p).mpr hp) y

namespace NormalizedSimplexIdentities

/-- The Street realization and its actual singular realization have the same
weak-equivalence test, without Gray or Kan–Quillen assumptions. -/
theorem streetWeak_iff_singular_realization (h : NormalizedSimplexIdentities)
    {C D : StrictOmegaCategory.{0}} (f : C ⟶ D) :
    h.streetWeakEquivalences f ↔ realizationWeakEquivalences
      (TopCat.toSSet.map (SSet.toTop.map (h.streetNerve.map f))) :=
  (singular_map_weak_iff (SSet.toTop.map (h.streetNerve.map f))).symm

/-- The same equivalence in every finite strict dimension. -/
theorem finiteStreetWeak_iff_singular_realization (h : NormalizedSimplexIdentities) (n : ℕ)
    {C D : StrictOmegaCategory.Truncated (n+1)} (f : C ⟶ D) :
    (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))) f ↔ realizationWeakEquivalences
      (TopCat.toSSet.map (SSet.toTop.map ((h.finiteStreetNerve (n+1)).map f))) :=
  (singular_map_weak_iff (SSet.toTop.map ((h.finiteStreetNerve (n+1)).map f))).symm

/-- Actual singular path objects give the same strict Street weak test. -/
theorem streetWeak_iff_singular_path_internalHom (h : NormalizedSimplexIdentities)
    {C D : StrictOmegaCategory.{0}} (f : C ⟶ D) :
    h.streetWeakEquivalences f ↔ realizationWeakEquivalences
      ((ihom (Δ[1] : SSet.{0})).map
        (TopCat.toSSet.map (SSet.toTop.map (h.streetNerve.map f)))) :=
  (singular_path_internalHom_weak_iff (SSet.toTop.map (h.streetNerve.map f))).symm

end NormalizedSimplexIdentities

end

end Thomason.Construction

end

section

/-! # Continuous homotopy inverses for the actual strict Street weak test -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory

noncomputable section

/-- A strict higher functor is Street weak precisely when its actual
realized Street nerve admits a continuous homotopy inverse. -/
theorem streetWeak_iff_homotopyEquiv (h : NormalizedSimplexIdentities)
    {C D : StrictOmegaCategory.{0}} (f : C ⟶ D) :
    h.streetWeakEquivalences f ↔
      ∃ e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj (h.streetNerve.obj C))
          (SSet.toTop.obj (h.streetNerve.obj D)),
        e.toFun = (SSet.toTop.map (h.streetNerve.map f)).hom :=
  realization_weak_iff_homotopyEquiv (h.streetNerve.map f)

/-- The same actual homotopy-inverse criterion holds in every positive
finite strict dimension, with the original finite Street nerve. -/
theorem finiteStreetWeak_iff_homotopyEquiv (h : NormalizedSimplexIdentities) (n : ℕ)
    {C D : StrictOmegaCategory.Truncated (n+1)} (f : C ⟶ D) :
    (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))) f ↔
      ∃ e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj ((h.finiteStreetNerve (n+1)).obj C))
          (SSet.toTop.obj ((h.finiteStreetNerve (n+1)).obj D)),
        e.toFun = (SSet.toTop.map ((h.finiteStreetNerve (n+1)).map f)).hom :=
  realization_weak_iff_homotopyEquiv ((h.finiteStreetNerve (n+1)).map f)

/-- An actual full inclusion that is Street weak retracts continuously,
with its complete realized full subcategory fixed throughout the deformation. -/
theorem fullInclusion_streetWeak_deformation (h : NormalizedSimplexIdentities)
    (C : StrictOmegaCategory.{0}) (S : Set C)
    (hw : h.streetWeakEquivalences (C.fullInclusion S)) :
    ∃ r : SSet.toTop.obj (h.streetNerve.obj C) ⟶
        SSet.toTop.obj (h.streetNerve.obj (C.fullOn S)),
      SSet.toTop.map (h.streetNerve.map (C.fullInclusion S)) ≫ r = 𝟙 _ ∧
      Nonempty ((r ≫ SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom.HomotopyRel
        (ContinuousMap.id _)
        (Set.range (SSet.toTop.map (h.streetNerve.map (C.fullInclusion S))).hom)) := by
  apply weak_mono_realization_deformation _ hw

end

end Thomason.Construction.NormalizedSimplexIdentities

end

end OAI
