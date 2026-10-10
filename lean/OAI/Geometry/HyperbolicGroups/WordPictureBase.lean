import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonSphereFurther
import OAI.Geometry.HyperbolicGroups.WordPicture

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

lemma finRange_boundary (n : ℕ) : IsBoundary (finRotate n) (List.finRange n) := by
  refine ⟨List.nodup_finRange n,?_⟩
  intro x _
  let : NeZero n := x.neZero
  have hi : x.val < (List.finRange n).length := by simp
  have hh := List.formPerm_apply_getElem (List.finRange n) (List.nodup_finRange n) x.val hi
  simp only [List.length_finRange,List.getElem_finRange] at hh
  have he : (List.finRange n).formPerm x = ⟨(x.val+1)%n,Nat.mod_lt _ (NeZero.pos n)⟩ := hh
  rw [he,finRotate_apply]
  apply Fin.ext
  change (x.val + 1 % n) % n = (x.val + 1) % n
  exact Nat.add_mod_mod _ _ _

end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture

/-- The two sides of a genuine relator disk and its distinguished exterior.
Every side is separately indexed, even when its letter is repeated. -/
def polygon (hw : w ∈ R) (hne : w ≠ []) : WordPicture R w where
  Dart := Bool × Fin w.length
  pairing := PolygonSphere.pairing (finRotate w.length)
  genusZero := PolygonSphere.genusZero _
    (fun i j => (finRange_boundary _).sameCycle (List.mem_finRange i) (List.mem_finRange j))
    ⟨0,List.length_pos_iff.mpr hne⟩
  label := fun x => if x.1 then w[x.2.val] else invLetter w[x.2.val]
  paired := by
    rintro ⟨b,i⟩
    cases b <;> simp [PolygonSphere.pairing,PolygonSphere.flip,invLetter_invLetter]
  outside := (List.finRange w.length).map (fun i => (true,i))
  boundary := (finRange_boundary _).map (fun i => (true,i))
    (fun i j h => congrArg Prod.snd h) (fun _ => rfl)
  word := by
    simp only [List.map_map,Function.comp_def,ite_true]
    exact List.map_getElem_finRange w
  interior := by
    rintro ⟨b,i⟩ hx
    cases b with
    | true => exact False.elim (hx (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    | false =>
      refine ⟨(List.finRange w.length).reverse.map (fun i => (false,i)),
        (finRange_boundary _).reverse.map (fun i => (false,i))
          (fun i j h => congrArg Prod.snd h) (fun _ => rfl),?_,?_⟩
      · exact List.mem_map.mpr ⟨i,by simp,rfl⟩
      · have he : List.map (fun x : Bool × Fin w.length => if x.1 then w[x.2.val] else invLetter w[x.2.val])
            ((List.finRange w.length).reverse.map (fun i => (false,i))) = FreeGroup.invRev w := by
          simp only [List.map_map,Function.comp_def,Bool.false_eq_true,ite_false,List.map_reverse]
          change ((List.finRange w.length).map (invLetter ∘ fun i => w[i.val])).reverse = _
          rw [← List.map_map,List.map_getElem_finRange]
          rfl
        rw [he]
        exact Or.inr (by simpa using hw)

lemma of_relator (hw : w ∈ R) : Nonempty (WordPicture R w) := by
  by_cases h : w = []
  · subst w; exact ⟨empty R⟩
  · exact ⟨polygon hw h⟩

/-- A freely canceling pair is the boundary of a single thickened edge,
with no interior cell. -/
def freePair (R : Set (Word A)) (a : A × Bool) : WordPicture R [a,invLetter a] where
  Dart := Bool
  pairing := {
    face := swap false true
    edge := swap false true
    edge_sq := swap_mul_self _ _
    edge_ne := by intro b; cases b <;> decide }
  genusZero := by
    let M : PictureMap Bool := {
      face := swap false true
      edge := swap false true
      edge_sq := swap_mul_self _ _
      edge_ne := by intro b; cases b <;> decide }
    change M.GenusZero
    have hc : ∀ x y, M.components x y := by
      intro x y
      cases x <;> cases y
      · exact M.components.refl' _
      · exact M.edge_le_components (SameCycle.rfl (f := M.edge) (x := false)).apply_right
      · exact M.edge_le_components (SameCycle.rfl (f := M.edge) (x := true)).apply_right
      · exact M.components.refl' _
    let : Subsingleton (Quotient M.components) := ⟨by
      intro x y
      induction x,y using Quotient.inductionOn₂ with
      | h x y => exact Quotient.sound (hc x y)⟩
    have hd : Nat.card (Quotient M.components) = 1 := Nat.card_unique
    change M.euler = 2 * (Nat.card (Quotient M.components) : ℤ)
    rw [hd]
    norm_num [M,PictureMap.euler,PictureMap.vertex,cycles,defect]
    rw [isSwap_iff_cycleType.mp (show (swap false true).IsSwap from ⟨false,true,by decide,rfl⟩)]
    norm_num
  label := fun b => if b then invLetter a else a
  paired := by
    intro b
    cases b <;> simp [invLetter_invLetter]
  outside := [false,true]
  boundary := ⟨by simp,fun _ _ => rfl⟩
  word := rfl
  interior := by intro b hb; cases b <;> exact False.elim (hb (by simp))

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
