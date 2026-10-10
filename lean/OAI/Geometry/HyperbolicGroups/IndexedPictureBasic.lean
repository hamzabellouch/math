import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureExist
import OAI.Geometry.HyperbolicGroups.IndexedWordPicture
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList

namespace OAI

/-! Exact cell disks, free spurs and cyclic basepoint changes with persistent
cell-side identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {w : Word E} {B : PolygonTarget.Boundary C (E × Bool) V}

namespace Indexing

def empty (B : PolygonTarget.Boundary C (E × Bool) V) (R : Set (Word E)) :
    Indexing B (WordPicture.empty R) where
  index := PEmpty.elim
  outside := fun x => PEmpty.elim x
  commute := fun x => PEmpty.elim x
  injective := fun {x} => PEmpty.elim x
  label := fun x => PEmpty.elim x

lemma empty_chain (weight : C → A) : (empty B R).chain weight = 0 := by
  change (∑ x : PEmpty, cornerWeight (B := B) weight (PEmpty.elim x)) = 0
  exact Finset.sum_eq_zero (fun x _ => PEmpty.elim x)

def freePair (B : PolygonTarget.Boundary C (E × Bool) V) (R : Set (Word E)) (a : E × Bool) :
    Indexing B (WordPicture.freePair R a) where
  index _ := none
  outside x := by
    change Bool at x
    change (none : Option B.Side) = none ↔ x ∈ ([false,true] : List Bool)
    refine iff_of_true rfl ?_
    cases x with
    | false => exact List.mem_cons_self
    | true => exact List.mem_cons_of_mem _ List.mem_cons_self
  commute _ := rfl
  injective := by intros; contradiction
  label := by intros; contradiction

lemma freePair_chain (weight : C → A) (a : E × Bool) : (freePair B R a).chain weight = 0 := by
  simp [chain,freePair,cornerWeight]

def rotate {P : WordPicture R w} (I : Indexing B P) (k : ℕ) : Indexing B (P.rotate k) where
  index := I.index
  outside x := by
    change P.Dart at x
    exact (I.outside x).trans List.mem_rotate.symm
  commute := I.commute
  injective := I.injective
  label := I.label

lemma rotate_chain {P : WordPicture R w} (I : Indexing B P) (weight : C → A) (k : ℕ) :
    (I.rotate k).chain weight = I.chain weight := rfl
end Indexing

variable (B) (hrev : B.rev = invLetter) (c : C)
/-- The literal indicated cell, not a reselected word-equivalent relator. -/
def cellDisk : WordPicture (Set.range B.attachingWord) (B.attachingWord c) where
  Dart := Bool × Fin (B.size c)
  pairing := PolygonSphere.pairing (finRotate (B.size c))
  genusZero := PolygonSphere.genusZero _
    (fun i j => (finRange_boundary _).sameCycle (List.mem_finRange i) (List.mem_finRange j))
    ⟨0,B.positive c⟩
  label x := if x.1 then B.label c x.2 else invLetter (B.label c x.2)
  paired := by
    rintro ⟨b,i⟩
    cases b <;> simp [PolygonSphere.pairing,PolygonSphere.flip,invLetter_invLetter]
  outside := (List.finRange (B.size c)).map (fun i => (true,i))
  boundary := (finRange_boundary _).map (fun i => (true,i))
    (fun i j h => congrArg Prod.snd h) (fun _ => rfl)
  word := by
    simp only [List.map_map,Function.comp_def,ite_true]
    exact List.ofFn_eq_map.symm
  interior := by
    rintro ⟨b,i⟩ hx
    cases b with
    | true => exact False.elim (hx (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    | false =>
      refine ⟨(List.finRange (B.size c)).reverse.map (fun i => (false,i)),
        (finRange_boundary _).reverse.map (fun i => (false,i))
          (fun i j h => congrArg Prod.snd h) (fun _ => rfl),?_,?_⟩
      · exact List.mem_map.mpr ⟨i,by simp,rfl⟩
      · right
        refine ⟨c,?_⟩
        simp only [List.map_map,Function.comp_def,Bool.false_eq_true,ite_false,List.map_reverse]
        symm
        change FreeGroup.invRev (((List.finRange (B.size c)).map (invLetter ∘ B.label c)).reverse) = _
        rw [←List.map_map,←List.ofFn_eq_map]
        change FreeGroup.invRev (FreeGroup.invRev (B.attachingWord c)) = _
        exact FreeGroup.invRev_invRev

def cellDiskIndex : Indexing B (cellDisk B c) where
  index x := if x.1 then none else some ⟨c,false,x.2⟩
  outside x := by
    change Bool × Fin (B.size c) at x
    rcases x with ⟨b,i⟩
    have ht : (true,i) ∈ (List.finRange (B.size c)).map (fun j => (true,j)) :=
      List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    have hf : (false,i) ∉ (List.finRange (B.size c)).map (fun j => (true,j)) := by
      rintro h
      obtain ⟨j,_,he⟩ := List.mem_map.mp h
      have he := congrArg Prod.fst he
      cases he
    cases b with
    | false => exact iff_of_false (Option.some_ne_none _) hf
    | true => exact iff_of_true rfl ht
  commute x := by
    rcases x with ⟨b,i⟩
    cases b <;> rfl
  injective := by
    rintro ⟨b,i⟩ ⟨b',j⟩ hxy s hi hj
    cases b <;> cases b' <;> simp only [Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,
      reduceCtorEq] at hi hj
    subst s
    have hij : i = j := by simpa using hj.symm
    exact congrArg (fun k => (false,k)) hij
  label x s hx := by
    rcases x with ⟨b,i⟩
    cases b with
    | true => contradiction
    | false =>
      simp only [Bool.false_eq_true,ite_false,Option.some.injEq] at hx
      subst s
      change invLetter (B.label c i) = B.rev (B.label c i)
      rw [hrev]

lemma cellDisk_chain (weight : C → A) :
    (cellDiskIndex B hrev c).chain weight = -weight c := by
  classical
  change (∑ x : Bool × Fin (B.size c), Indexing.cornerWeight weight
    (if x.1 then none else some ⟨c,false,x.2⟩)) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,Indexing.cornerWeight,
    PolygonTarget.Boundary.weight,Finset.sum_const_zero]
  have he : (∑ i : Fin (B.size c), if i.val = 0 then -weight c else 0) = -weight c := by
    have hh : ∀ i : Fin (B.size c), i.val = 0 ↔ i = ⟨0,B.positive c⟩ := fun i => by simp only [Fin.ext_iff]
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simpa only [zero_add] using he

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
