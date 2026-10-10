import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler
import OAI.Geometry.HyperbolicGroups.PictureRestrict
import OAI.Geometry.HyperbolicGroups.PictureMapFurther
import OAI.Geometry.HyperbolicGroups.DipoleSwitch

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I : Type*}
namespace PictureMap

/-- The darts of the two particular face occurrences being cancelled. -/
def InDipole (a b : I → D) (x : D) : Prop := (∃ i, a i = x) ∨ ∃ i, b i = x

namespace OppositeFaces
variable {f : Perm D} {q : Perm I} {a b : I → D} (h : OppositeFaces f q a b)
include h

lemma range_a_invariant (x : D) : (∃ i, a i = f x) ↔ ∃ i, a i = x := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨q.symm i,f.injective ?_⟩
    rw [h.a_face,q.apply_symm_apply]
    exact hi
  · rintro ⟨i,rfl⟩
    exact ⟨q i,(h.a_face i).symm⟩

lemma range_b_invariant (x : D) : (∃ i, b i = f x) ↔ ∃ i, b i = x := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨q i,f.injective ((h.b_face i).trans hi)⟩
  · rintro ⟨i,rfl⟩
    exact ⟨q.symm i,by simpa only [q.apply_symm_apply] using (h.b_face (q.symm i)).symm⟩

lemma inDipole_face (x : D) : InDipole a b (f x) ↔ InDipole a b x :=
  or_congr (h.range_a_invariant x) (h.range_b_invariant x)

lemma a_sameCycle [Fintype I] (i j : I) : f.SameCycle (a i) (a j) := by
  have hh : SameCycle.setoid q ≤ (SameCycle.setoid f).comap a := by
    apply sameCycle_le_of_apply
    intro k
    change f.SameCycle (a k) (a (q k))
    rw [← h.a_face]
    exact SameCycle.rfl.apply_right
  exact hh (h.cyclic i j)

lemma b_sameCycle [Fintype I] (i j : I) : f.SameCycle (b i) (b j) := by
  have hh : SameCycle.setoid q ≤ (SameCycle.setoid f).comap b := by
    apply sameCycle_le_of_apply
    intro k
    change f.SameCycle (b k) (b (q k))
    rw [← h.b_face]
    exact SameCycle.rfl.apply_left
  exact hh (h.cyclic i j)

lemma not_sameCycle_ab [Fintype D] (i j : I) : ¬ f.SameCycle (a i) (b j) := by
  intro hab
  have hh := invariant_of_sameCycle (P := fun x => ∃ i, a i = x) f h.range_a_invariant hab
  obtain ⟨k,hk⟩ := hh.mp ⟨i,rfl⟩
  exact h.disjoint k j hk

/-- Exactly the two face classes, not an arbitrary assumed two-cell subset. -/
def dipoleClassesEquiv [Fintype D] [Fintype I] (i₀ : I) : Bool ≃
    Quotient ((SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D)) := by
  let g : Bool → Quotient ((SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D)) :=
    fun t => if t then Quotient.mk _ ⟨b i₀,Or.inr ⟨i₀,rfl⟩⟩ else Quotient.mk _ ⟨a i₀,Or.inl ⟨i₀,rfl⟩⟩
  refine Equiv.ofBijective g ⟨?_,?_⟩
  · intro x y hxy
    cases x <;> cases y
    · rfl
    · exact False.elim (h.not_sameCycle_ab i₀ i₀ (Quotient.exact hxy))
    · exact False.elim (h.not_sameCycle_ab i₀ i₀ (Quotient.exact hxy.symm))
    · rfl
  · intro x
    induction x using Quotient.inductionOn with
    | h x =>
      rcases x.property with ⟨i,hi⟩ | ⟨i,hi⟩
      · refine ⟨false,Quotient.sound ?_⟩
        change f.SameCycle (a i₀) x.val
        rw [← hi]
        exact h.a_sameCycle i₀ i
      · refine ⟨true,Quotient.sound ?_⟩
        change f.SameCycle (b i₀) x.val
        rw [← hi]
        exact h.b_sameCycle i₀ i

lemma cycles_dipole [DecidableEq D] [Fintype D] [Fintype I] (i₀ : I) :
    cycles (f.subtypePerm h.inDipole_face) = 2 := by
  rw [cycles_eq_card_classes]
  have he : Nat.card (Quotient (SameCycle.setoid (f.subtypePerm h.inDipole_face))) =
      Nat.card (Quotient ((SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D))) :=
    Nat.card_congr (Quotient.congrRight (sameCycle_subtypePerm_iff f h.inDipole_face))
  rw [he,← Nat.card_congr (h.dipoleClassesEquiv i₀)]
  norm_num

end OppositeFaces
variable (M : PictureMap D) {q : Perm I} {a b : I → D}

lemma inDipole_edge (hp : ∀ i, M.edge (a i) = b i) (x : D) :
    InDipole a b (M.edge x) ↔ InDipole a b x := by
  have hfwd : ∀ x, InDipole a b x → InDipole a b (M.edge x) := by
    intro x hx
    rcases hx with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact Or.inr ⟨i,(hp i).symm⟩
    · exact Or.inl ⟨i,(M.paired_reverse (hp i)).symm⟩
  constructor
  · intro hx
    simpa only [M.edge_edge] using hfwd (M.edge x) hx
  · exact hfwd x

/-- Delete the isolated dipole; every unremoved face and dart retains its
original index, and every surviving side pairing is unchanged. -/
def removeDipole (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i) :
    PictureMap {x : D // ¬ InDipole a b x} :=
  M.restrict _ (fun x => not_congr (hF.inDipole_face x)) (fun x => not_congr (M.inDipole_edge hp x))

lemma removeDipole_genusZero [DecidableEq D] [Fintype D]
    (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i)
    (hG : M.GenusZero) : (M.removeDipole hF hp).GenusZero := by
  classical
  convert M.restrict_genusZero (fun x => ¬ InDipole a b x) hG
    (fun x => not_congr (hF.inDipole_face x))
    (fun x => not_congr (M.inDipole_edge hp x)) using 1
  rfl

lemma removeDipole_faces [DecidableEq D] [Fintype D] [Fintype I]
    (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i) (i₀ : I) :
    cycles (M.removeDipole hF hp).face = cycles M.face - 2 := by
  have hh := cycles_subtype_split M.face hF.inDipole_face
  rw [hF.cycles_dipole i₀] at hh
  change cycles (M.face.subtypePerm (fun x => not_congr (hF.inDipole_face x))) = _
  omega

lemma restrict_respects {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (P : D → Prop)
    (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).Respects (label ∘ Subtype.val) start rev := by
  constructor
  · intro x; exact hM.1 x.val
  · intro x; exact hM.2 x.val

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
