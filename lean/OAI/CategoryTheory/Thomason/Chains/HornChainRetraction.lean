import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting

namespace OAI

section

/-! # A second-subdivision retraction into the first-subdivided horn

For a chain of faces, keep the maxima of its horn faces. If an excluded
face occurs, add the distinguished horn vertex. On chains entirely in the
horn this is exactly the image under the original last-vertex operation.
-/

namespace Thomason.Construction.HornChainRetraction

open PartialOrder SubdivisionHornFaces
open scoped Classical

noncomputable section

def good (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) : Finset (Faces n) :=
  C.finset.filter (fun A => A ∈ hornFaceSet n k)

def bad (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) : Prop :=
  ∃ A ∈ C.finset, A ∉ hornFaceSet n k

def imageVertices (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) :
    Finset (ULift.{0} (Fin (n+2))) :=
  (good n k C).image chainMaximum ∪ if bad n k C then {ULift.up k} else ∅

theorem good_mem {n : ℕ} {k : Fin (n+2)} {C : NonemptyFiniteChains (Faces n)} {A : Faces n} :
    A ∈ good n k C ↔ A ∈ C.finset ∧ A ∈ hornFaceSet n k := Finset.mem_filter

theorem imageVertices_nonempty (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) :
    (imageVertices n k C).Nonempty := by
  obtain ⟨A, hA⟩ := C.nonempty
  by_cases hg : A ∈ hornFaceSet n k
  · exact ⟨chainMaximum A, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨A, good_mem.mpr ⟨hA, hg⟩, rfl⟩)⟩
  · have hb : bad n k C := ⟨A, hA, hg⟩
    refine ⟨ULift.up k, Finset.mem_union_right _ ?_⟩
    simp only [hb, ↓reduceIte, Finset.mem_singleton]

theorem good_greatest (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n))
    (h : (good n k C).Nonempty) :
    ∃ M ∈ good n k C, ∀ A ∈ good n k C, A ≤ M := by
  obtain ⟨M, hM, hm⟩ := Finset.exists_max_image (good n k C) (fun A => A.finset.card) h
  refine ⟨M, hM, fun A hA => ?_⟩
  rcases C.comparable ⟨A, (good_mem.mp hA).1⟩ ⟨M, (good_mem.mp hM).1⟩ with hle | hle
  · exact hle
  · have he : M.finset = A.finset := Finset.eq_of_subset_of_card_le hle (hm A hA)
    exact he.symm.le

theorem imageVertices_omits (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) :
    ∃ j : Fin (n+2), j ≠ k ∧ ULift.up j ∉ imageVertices n k C := by
  by_cases hg : (good n k C).Nonempty
  · obtain ⟨M, hM, hm⟩ := good_greatest n k C hg
    obtain ⟨j, hj, hnot⟩ := (hornFaceSet_iff n k M).mp (good_mem.mp hM).2
    refine ⟨j, hj, ?_⟩
    intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨A, hA, he⟩ := Finset.mem_image.mp hv
      apply hnot
      apply hm A hA
      rw [← he]
      exact Finset.max'_mem A.finset A.nonempty
    · by_cases hb : bad n k C
      · simp only [hb, ↓reduceIte, Finset.mem_singleton] at hv
        exact hj (congrArg ULift.down hv)
      · simp only [hb, ↓reduceIte, Finset.notMem_empty] at hv
  · have he : good n k C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hg
    have hne : ∃ j : Fin (n+2), j ≠ k := by
      by_cases hk : k = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro h
        have hh := congrArg Fin.val h
        rw [hk] at hh
        simp at hh
      · exact ⟨0, Ne.symm hk⟩
    obtain ⟨j, hj⟩ := hne
    refine ⟨j, hj, ?_⟩
    intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · simp only [he, Finset.image_empty, Finset.notMem_empty] at hv
    · by_cases hb : bad n k C
      · simp only [hb, ↓reduceIte, Finset.mem_singleton] at hv
        exact hj (congrArg ULift.down hv)
      · simp only [hb, ↓reduceIte, Finset.notMem_empty] at hv

def face (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) : Faces n where
  finset := imageVertices n k C
  nonempty := imageVertices_nonempty n k C
  comparable a b := le_total a.val b.val

theorem face_mem (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n)) :
    face n k C ∈ hornFaceSet n k :=
  (hornFaceSet_iff n k _).mpr (imageVertices_omits n k C)

theorem imageVertices_mono (n : ℕ) (k : Fin (n+2))
    {C D : NonemptyFiniteChains (Faces n)} (h : C ≤ D) :
    imageVertices n k C ⊆ imageVertices n k D := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨A, good_mem.mpr ⟨h (good_mem.mp hA).1, (good_mem.mp hA).2⟩, rfl⟩)
  · by_cases hb : bad n k C
    · have hd : bad n k D := by
        obtain ⟨A, hA, ha⟩ := hb
        exact ⟨A, h hA, ha⟩
      apply Finset.mem_union_right
      simpa only [hb, hd, ↓reduceIte] using hx
    · simp only [hb, ↓reduceIte, Finset.notMem_empty] at hx

def retraction (n : ℕ) (k : Fin (n+2)) :
    NonemptyFiniteChains (Faces n) →o HornFaces n k where
  toFun C := ⟨⟨face n k C, (face_mem n k C).1⟩, (face_mem n k C).2⟩
  monotone' _ _ h := imageVertices_mono n k h

/-- On old chains no additional vertex is inserted: the operation is
precisely the finite-chain image under the original greatest-vertex map. -/
theorem retraction_old (n : ℕ) (k : Fin (n+2)) (C : NonemptyFiniteChains (Faces n))
    (hC : ∀ A ∈ C.finset, A ∈ hornFaceSet n k) :
    (retraction n k C).val.val = C.map chainMaximumHom := by
  apply NonemptyFiniteChains.ext
  have hg : good n k C = C.finset := Finset.filter_true_of_mem hC
  have hb : ¬ bad n k C := by
    rintro ⟨A, hA, ha⟩
    exact ha (hC A hA)
  change imageVertices n k C = _
  simp only [imageVertices, hg, hb, ↓reduceIte, Finset.union_empty,
    NonemptyFiniteChains.map, chainMaximumHom]
  ext x
  simp only [Finset.mem_image]
  rfl

end

end Thomason.Construction.HornChainRetraction

end

end OAI
