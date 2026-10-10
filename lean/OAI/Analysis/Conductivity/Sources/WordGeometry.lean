import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalOpenBlock

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceChildEuclidean_eq_similarity (σ : ℝ) : sourceChildEuclidean σ=sourceSimilarity σ := by
  apply Homeomorph.ext
  intro x
  exact sourceChild_toLp σ (WithLp.ofLp x)

lemma source_child_closed_subset (k : Fin 2) :
    sourceChildEuclidean (actualChildSign k) '' closure sourceDomain⊆sourceDomain := by
  rw [sourceChildEuclidean_eq_similarity]
  fin_cases k
  · exact source_children_compact_inside.2.2.1
  · exact source_children_compact_inside.2.2.2.1

lemma source_child_closed_disjoint {k l : Fin 2} (h : k≠l) :
    Disjoint (sourceChildEuclidean (actualChildSign k) '' closure sourceDomain)
      (sourceChildEuclidean (actualChildSign l) '' closure sourceDomain) := by
  rw [sourceChildEuclidean_eq_similarity,sourceChildEuclidean_eq_similarity]
  fin_cases k <;> fin_cases l
  · exact (h rfl).elim
  · exact source_children_compact_inside.2.2.2.2
  · exact source_children_compact_inside.2.2.2.2.symm
  · exact (h rfl).elim

abbrev SourceWord := List (Fin 2)

def sourceWordMap : SourceWord → R3 ≃ₜ R3
  | [] => Homeomorph.refl R3
  | k::ν => (sourceWordMap ν).trans (sourceChildEuclidean (actualChildSign k))

@[simp] lemma sourceWordMap_nil (x : R3) : sourceWordMap [] x=x := rfl
@[simp] lemma sourceWordMap_cons (k : Fin 2) (ν : SourceWord) (x : R3) :
    sourceWordMap (k::ν) x=sourceChildEuclidean (actualChildSign k) (sourceWordMap ν x) := rfl

lemma sourceWordMap_append (ν ω : SourceWord) (x : R3) :
    sourceWordMap (ν++ω) x=sourceWordMap ν (sourceWordMap ω x) := by
  induction ν with
  | nil => rfl
  | cons k ν ih => simp only [List.cons_append,sourceWordMap_cons,ih]

lemma sourceWordMap_dist (ν : SourceWord) (x y : R3) :
    dist (sourceWordMap ν x) (sourceWordMap ν y)=sourceScale^ν.length*dist x y := by
  induction ν with
  | nil => simp
  | cons k ν ih =>
    simp only [sourceWordMap_cons,sourceChildEuclidean_eq_similarity,sourceSimilarity_dist,ih,List.length_cons,pow_succ]
    ring

lemma sourceWordMap_closed_subset (ν : SourceWord) : sourceWordMap ν '' closure sourceDomain⊆closure sourceDomain := by
  induction ν with
  | nil =>
    rintro _ ⟨x,hx,rfl⟩
    exact hx
  | cons k ν ih =>
    rintro _ ⟨x,hx,rfl⟩
    exact subset_closure (source_child_closed_subset k ⟨sourceWordMap ν x,ih ⟨x,hx,rfl⟩,rfl⟩)

def sourceWordCell (ν : SourceWord) : Set R3 := sourceWordMap ν '' closure sourceDomain

def sourceWordBlock (ν : SourceWord) : Set R3 := sourceWordMap ν '' sourceOpenBlock

lemma sourceWordCell_subset (ν : SourceWord) : sourceWordCell ν⊆closure sourceDomain := sourceWordMap_closed_subset ν

lemma sourceWordBlock_subset_cell (ν : SourceWord) : sourceWordBlock ν⊆sourceWordCell ν :=
  image_mono (fun _ h => subset_closure h.1)

lemma sourceWordBlock_isOpen (ν : SourceWord) : IsOpen (sourceWordBlock ν) :=
  (sourceWordMap ν).isOpenMap _ sourceOpenBlock_isOpen

lemma sourceWordCell_isCompact (ν : SourceWord) : IsCompact (sourceWordCell ν) :=
  sourceClosure_isCompact.image (sourceWordMap ν).continuous

lemma sourceWordCell_cons_subset (k : Fin 2) (ν : SourceWord) :
    sourceWordCell (k::ν)⊆sourceChildEuclidean (actualChildSign k) '' closure sourceDomain := by
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨sourceWordMap ν x,sourceWordMap_closed_subset ν ⟨x,hx,rfl⟩,rfl⟩

lemma sourceWordBlock_cons (k : Fin 2) (ν : SourceWord) :
    sourceWordBlock (k::ν)=sourceChildEuclidean (actualChildSign k) '' sourceWordBlock ν := by
  change (fun x => sourceChildEuclidean (actualChildSign k) (sourceWordMap ν x)) '' sourceOpenBlock =
    sourceChildEuclidean (actualChildSign k) '' (sourceWordMap ν '' sourceOpenBlock)
  exact (image_image _ _ _).symm

lemma sourceWordBlock_nil_cons_disjoint (k : Fin 2) (ν : SourceWord) :
    Disjoint (sourceWordBlock []) (sourceWordBlock (k::ν)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : x∈sourceOpenBlock := by
    rcases hx with ⟨y,hey,rfl⟩
    exact hey
  apply hx'.2
  apply mem_iUnion.mpr
  refine ⟨k,?_⟩
  rw [←sourceChildEuclidean_eq_similarity]
  exact sourceWordCell_cons_subset k ν (sourceWordBlock_subset_cell _ hy)

lemma sourceWordBlock_disjoint {ν ω : SourceWord} (h : ν≠ω) :
    Disjoint (sourceWordBlock ν) (sourceWordBlock ω) := by
  induction ν generalizing ω with
  | nil =>
    cases ω with
    | nil => exact (h rfl).elim
    | cons k ω => exact sourceWordBlock_nil_cons_disjoint k ω
  | cons k ν ih =>
    cases ω with
    | nil => exact (sourceWordBlock_nil_cons_disjoint k ν).symm
    | cons l ω =>
      by_cases hkl : k=l
      · subst l
        have hn : ν≠ω := fun hn => h (congrArg (List.cons k) hn)
        rw [sourceWordBlock_cons,sourceWordBlock_cons]
        apply Set.disjoint_left.mpr
        rintro x ⟨y,hy,he⟩ ⟨z,hz,hf⟩
        have hez : y=z := (sourceChildEuclidean (actualChildSign k)).injective (he.trans hf.symm)
        subst z
        exact Set.disjoint_left.mp (ih hn) hy hz
      · exact (source_child_closed_disjoint hkl).mono
          ((sourceWordBlock_subset_cell _).trans (sourceWordCell_cons_subset k ν))
          ((sourceWordBlock_subset_cell _).trans (sourceWordCell_cons_subset l ω))

lemma sourceWordBlock_unique {x : R3} {ν ω : SourceWord}
    (hν : x∈sourceWordBlock ν) (hω : x∈sourceWordBlock ω) : ν=ω := by
  by_contra hn
  exact Set.disjoint_left.mp (sourceWordBlock_disjoint hn) hν hω

lemma sourceWordBlock_root : sourceWordBlock []=sourceOpenBlock := by
  ext x
  simp [sourceWordBlock,sourceWordMap]

lemma sourceWordBlock_child_iff (k : Fin 2) {x : R3} (hx : x∈closure sourceDomain) (ν : SourceWord) :
    sourceChildEuclidean (actualChildSign k) x∈sourceWordBlock ν ↔
      ∃ ω : SourceWord,ν=k::ω ∧ x∈sourceWordBlock ω := by
  constructor
  · intro hν
    cases ν with
    | nil =>
      rw [sourceWordBlock_root] at hν
      exact (hν.2 (mem_iUnion.mpr ⟨k,by rw [←sourceChildEuclidean_eq_similarity]; exact ⟨x,hx,rfl⟩⟩)).elim
    | cons l ν =>
      have hl : k=l := by
        by_contra hn
        exact Set.disjoint_left.mp (source_child_closed_disjoint hn) ⟨x,hx,rfl⟩
          (sourceWordCell_cons_subset l ν (sourceWordBlock_subset_cell _ hν))
      subst l
      rw [sourceWordBlock_cons] at hν
      exact ⟨ν,rfl,(sourceChildEuclidean (actualChildSign k)).injective.mem_set_image.mp hν⟩
  · rintro ⟨ω,rfl,hω⟩
    rw [sourceWordBlock_cons]
    exact ⟨x,hω,rfl⟩

end ScalarConductivity

end
end

end OAI
