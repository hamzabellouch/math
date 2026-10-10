import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PolygonCommutingRepresentatives
import OAI.GroupTheory.SimpleAmenable.Homology.FullGroupStability

namespace OAI

section

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

namespace PolygonTracks
variable {a m n : ℕ}

noncomputable def castFull (a : ℕ) {m n : ℕ} (h : m=n) :
    polygonFullGroup a m ≃* polygonFullGroup a n := h ▸ MulEquiv.refl _

@[simp] lemma castFull_apply (h : m=n) (f : polygonFullGroup a m) (x : TrackPoint a m) :
    (castFull a h f).val (Fin.cast h x.1,x.2)=
      (Fin.cast h (f.val x).1,(f.val x).2) := by subst n; rfl

lemma stabilize_add (a k l n : ℕ) : stabilize a (k+l) n =
    (castFull a (Nat.add_assoc k l n).symm).toMonoidHom.comp
      ((stabilize a k (l+n)).comp (stabilize a l n)) := by
  let h : k+(l+n)=(k+l)+n := (Nat.add_assoc k l n).symm
  apply MonoidHom.ext
  intro f
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨i,hi⟩ := (finCongr h).surjective x.1
  change (stabilize a (k+l) n f).val x =
    (castFull a h (stabilize a k (l+n) (stabilize a l n f))).val x
  have hx : x=(Fin.cast h i,x.2) := Prod.ext hi.symm rfl
  rw [hx, castFull_apply (x:=(i,x.2))]
  induction i using Fin.addCases with
  | left i =>
    have he : Fin.cast h (i.castAdd (l+n))=(i.castAdd l).castAdd n := Fin.ext rfl
    rw [he, stabilize_left (x:=((i.castAdd l),x.2)), stabilize_left (x:=(i,x.2))]
    exact Prod.ext he.symm rfl
  | right i =>
    rw [stabilize_right (x:=(i,x.2))]
    induction i using Fin.addCases with
    | left i =>
      have he : Fin.cast h ((i.castAdd n).natAdd k)=(i.natAdd k).castAdd n := Fin.ext rfl
      rw [he, stabilize_left (x:=(i.natAdd k,x.2)), stabilize_left (x:=(i,x.2))]
      exact Prod.ext he.symm rfl
    | right i =>
      have he : Fin.cast h ((i.natAdd l).natAdd k)=i.natAdd (k+l) := by
        apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
      rw [he, stabilize_right (x:=(i,x.2)), stabilize_right (x:=(i,x.2))]
      apply Prod.ext
      · apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
      · rfl

lemma stabilize_zero_bijective (a n : ℕ) : Function.Bijective (stabilize a 0 n) := by
  refine ⟨stabilize_injective,?_⟩
  intro f
  let g : bankFixer a 0 n := ⟨f,fun x => Fin.elim0 x.1⟩
  exact ⟨restrict g,stabilize_restrict g⟩

lemma stabilize_H1_isIso (a k n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (stabilize a k n) 1) := by
  induction k with
  | zero =>
      exact TrivialHomology.isIso_equiv
        (MulEquiv.ofBijective (stabilize a 0 n) (stabilize_zero_bijective a n)) 1
  | succ k ih =>
    have he : IsIso (TrivialHomology.map (stabilize a (1+k) n) 1) := by
      rw [stabilize_add, TrivialHomology.map_comp, TrivialHomology.map_comp]
      have := TrivialHomology.isIso_equiv (castFull a (Nat.add_assoc 1 k n).symm) 1
      have := PolygonPlacement.Configuration.stabilize_H1_isIso a (k+n) (by omega)
      have := ih
      infer_instance
    rw [show k+1=1+k by omega]
    exact he

lemma stabilize_alternating_comap (a k n : ℕ) (hn : 32 ≤ n) :
    (polygonAlternatingGroup a (k+n)).comap (stabilize a k n)=polygonAlternatingGroup a n := by
  have := stabilize_H1_isIso a k n hn
  rw [← polygonFullGroup_commutator_eq a n (by omega),
    ← polygonFullGroup_commutator_eq a (k+n) (by omega)]
  exact TrivialHomology.commutator_comap_of_mono (stabilize a k n)

end PolygonTracks
end SimpleAmenable

end

end

end OAI
