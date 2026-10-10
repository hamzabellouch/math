import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Training
import OAI.Combinatorics.RamseyFive.Probability.MeasurePublicTable

namespace OAI

namespace SharpRamseyFive.GreedyTraining

section
open MeasurePublicTable
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

noncomputable def publicRegion {J : ℕ} (L : Fin J→Finset A) (i : Fin J) : Finset A :=
  (L i).filter fun x=>∀ j : Fin J, j < i → x ∉ L j

noncomputable def publicOwn {J : ℕ} (L : Fin J→Finset A) (x : A) : Finset A :=
  match firstIndex {B | x∈B} L with
  | none => ∅
  | some i => publicRegion L i

noncomputable def greedyList (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) : Fin J→Finset A := fun i=>shape (chosen F hF shape X i)

lemma firstIndex_greedyList (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) (x : A) :
    firstIndex {B | x∈B} (greedyList F hF shape X J)=queryPart F hF shape X J x := by
  cases he : firstIndex {B | x∈B} (greedyList F hF shape X J) with
  | none =>
    have hh := (firstIndex_none_iff _ _).mp he
    unfold queryPart
    have hn : ¬firstAt F hF shape X J x<J := by
      intro h
      exact hh ⟨_,h⟩ (firstAt_mem F hF shape X J x h)
    rw [dite_eq_right hn]
  | some i =>
    have hm := firstIndex_some_mem _ _ he
    have hmin := firstIndex_minimal _ _ he
    have hf : firstAt F hF shape X J x=i.val := by
      apply firstAt_eq F hF shape X J i.val x i.prop hm
      intro j hj
      exact hmin ⟨j,hj.trans i.prop⟩ hj
    unfold queryPart
    simp only [hf,dite_eq_left i.prop]

lemma region_cell (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) (i : Fin J) :
    X∩publicRegion (greedyList F hF shape X J) i=cell F hF shape X i := by
  ext x
  rw [cell_earliest]
  rw [Finset.mem_inter]
  change (x∈X ∧ x∈(shape (chosen F hF shape X i)).filter (fun x => ∀ j : Fin J, j < i → x∉shape (chosen F hF shape X j))) ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hx,hm,he⟩
    refine ⟨hx,hm,fun j hj=>he ⟨j,hj.trans i.prop⟩ hj⟩
  · rintro ⟨hx,hm,he⟩
    exact ⟨hx,hm,fun j hj=>he j.val hj⟩

lemma clipped_publicOwn (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (hSX : S⊆X) (J : ℕ) (x : A) :
    S∩publicOwn (greedyList F hF shape X J) x=
      clippedPart S F hF shape X J (queryPart F hF shape X J x) := by
  unfold publicOwn
  rw [firstIndex_greedyList]
  cases he : queryPart F hF shape X J x with
  | none => simp [clippedPart]
  | some i =>
    change S∩publicRegion (greedyList F hF shape X J) i=S∩cell F hF shape X i
    rw [←region_cell F hF shape X J i,←Finset.inter_assoc,Finset.inter_eq_left.mpr hSX]

lemma ownCell_subset_publicOwn (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) :
    ownCell F hF shape X J x⊆publicOwn (greedyList F hF shape X J) x := by
  have hh := clipped_publicOwn X F hF shape X (Finset.Subset.refl _) J x
  rw [clippedPart_query] at hh
  have hc : ownCell F hF shape X J x⊆X := by
    unfold ownCell
    split_ifs
    · exact (cell_subset F hF shape X _).trans (remaining_subset F hF shape X _)
    · exact Finset.empty_subset _
  rw [Finset.inter_eq_right.mpr hc] at hh
  exact hh▸Finset.inter_subset_right

end

open TrainingCells
open scoped Classical BigOperators
variable {A I J : Type*} [DecidableEq A] [LinearOrder I] [LinearOrder J]

noncomputable def twoPublicOwn {h p : ℕ} (LH : Fin h→Finset A) (LP : Fin p→Finset A)
    (x : A) : Finset A := publicOwn LH x∪publicOwn LP x

theorem literal_cell_data (S X Y : Finset A) (hSX : S⊆X) (hSY : S⊆Y)
    (H : Finset I) (hH : H.Nonempty) (hyper : I→Finset A) (h : ℕ)
    (P : Finset J) (hP : P.Nonempty) (plane : J→Finset A) (p : ℕ) :
    let CH := clippedPart S H hH hyper X h
    let CP := clippedPart S P hP plane Y p
    let C := family CH CP
    let ih := fun x => queryPart H hH hyper X h x
    let ip := fun x => queryPart P hP plane Y p x
    let raw := twoPublicOwn (greedyList H hH hyper X h) (greedyList P hP plane Y p)
    (∀i,C i⊆S) ∧ (∑i,(C i).card)≤3*S.card ∧
    (∀x,S∩raw x=C (.inl (ih x))∪C (.inr (.inl (ip x)))) ∧
    (∀x,C (.inr (.inr (ih x,ip x)))=C (.inl (ih x))∩C (.inr (.inl (ip x)))) ∧
    (∀x,ownCell H hH hyper X h x⊆raw x) ∧
    (∀x,ownCell P hP plane Y p x⊆raw x) := by
  dsimp only
  refine ⟨family_subsets S _ _ (clippedPart_subset S H hH hyper X h)
    (clippedPart_subset S P hP plane Y p),
    family_mass S _ _ (clippedPart_subset S H hH hyper X h)
      (clippedPart_subset S P hP plane Y p) (clippedPart_disjoint S H hH hyper X h)
      (clippedPart_disjoint S P hP plane Y p),?_,?_,?_,?_⟩
  · intro x
    change S∩(publicOwn (greedyList H hH hyper X h) x∪publicOwn (greedyList P hP plane Y p) x)=_
    rw [Finset.inter_union_distrib_left,clipped_publicOwn S H hH hyper X hSX,
      clipped_publicOwn S P hP plane Y hSY]
    rfl
  · intro x; rfl
  · intro x
    exact (ownCell_subset_publicOwn H hH hyper X h x).trans Finset.subset_union_left
  · intro x
    exact (ownCell_subset_publicOwn P hP plane Y p x).trans Finset.subset_union_right

lemma public_own_count (S X Y : Finset A) (hSX : S⊆X) (hSY : S⊆Y)
    (H : Finset I) (hH : H.Nonempty) (hyper : I→Finset A) (h : ℕ)
    (P : Finset J) (hP : P.Nonempty) (plane : J→Finset A) (p : ℕ) (x : A) :
    let CH := clippedPart S H hH hyper X h
    let CP := clippedPart S P hP plane Y p
    let ih := queryPart H hH hyper X h x
    let ip := queryPart P hP plane Y p x
    (S∩twoPublicOwn (greedyList H hH hyper X h) (greedyList P hP plane Y p) x).card=
      (CH ih).card+(CP ip).card-(CH ih∩CP ip).card := by
  dsimp only
  have he := (literal_cell_data S X Y hSX hSY H hH hyper h P hP plane p).2.2.1 x
  rw [he,Finset.card_union]
  rfl

lemma literal_small_own (S X Y : Finset A) (hS : S.Nonempty)
    (hSX : S⊆X) (hSY : S⊆Y)
    (H : Finset I) (hH : H.Nonempty) (hyper : I→Finset A) (h : ℕ)
    (P : Finset J) (hP : P.Nonempty) (plane : J→Finset A) (p : ℕ)
    (hsH : ∀i,((clippedPart S H hH hyper X h i).card:ℝ)≤(S.card:ℝ)/25)
    (hsP : ∀i,((clippedPart S P hP plane Y p i).card:ℝ)≤(S.card:ℝ)/25) (x : A) :
    ((S∩twoPublicOwn (greedyList H hH hyper X h) (greedyList P hP plane Y p) x).card:ℝ)/S.card≤2/25 := by
  have he := (literal_cell_data S X Y hSX hSY H hH hyper h P hP plane p).2.2.1 x
  rw [he]
  exact small_union S _ _ hS (hsH _) (hsP _)

end SharpRamseyFive.GreedyTraining

end OAI
