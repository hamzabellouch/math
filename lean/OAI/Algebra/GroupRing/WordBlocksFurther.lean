import Mathlib
import OAI.Algebra.GroupRing.WordBlocks
import OAI.Algebra.GroupRing.WordCursor

namespace OAI

section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
noncomputable section
variable {A G : Type*} [Group G] (v : A→G) {inv : A→A} {ws : List (List A)}
structure Lift (d : Matching inv ws) where
  position : Occ ws→G
  next : ∀i,position (BlockBoundary.rotation (lengths ws) i)=position i*v (letter ws i)
  pair : ∀i,position (d.partner i)=position i*v (letter ws i)
variable {v}
lemma cursor_rotation (w : List A) (hw : WordCursor.value v w=1) (i : Fin w.length) :
    WordCursor.cursor v w (finRotate w.length i).val=WordCursor.cursor v w i.val*v (w.get i) := by
  by_cases hi : i.val+1<w.length
  · have hh : (finRotate w.length i).val=i.val+1 := by
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w.length≠0)
      have aux : ∀j : Fin w.length,j.val+1<w.length→(finRotate w.length j).val=j.val+1 := by
        rw [hn]
        rintro ⟨j,hj⟩ hjj
        change j+1<n+1 at hjj
        exact congrArg Fin.val (finRotate_of_lt (by omega : j<n))
      exact aux i hi
    rw [hh]
    exact WordCursor.cursor_succ v w i
  · have he : i.val+1=w.length := by omega
    have h := WordCursor.cursor_succ v w i
    rw [he,WordCursor.cursor_length,hw] at h
    have hh : (finRotate w.length i).val=0 := by
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w.length≠0)
      have aux : ∀j : Fin w.length,j.val+1=w.length→(finRotate w.length j).val=0 := by
        rw [hn]
        intro j hj
        have hjj : j=Fin.last n := by apply Fin.ext; simp only [Fin.val_last];omega
        rw [hjj,finRotate_last]
        rfl
      exact aux i he
    rw [hh]
    exact h
lemma flat_rotation (ws : List (List A)) (h : ∀w∈ws,WordCursor.value v w=1) (i : Occ ws) :
    WordCursor.cursor v ws.flatten (coordinates ws (BlockBoundary.rotation (lengths ws) i)).val=
      WordCursor.cursor v ws.flatten (coordinates ws i).val*v (letter ws i) := by
  induction ws with
  | nil=>exact Empty.elim i
  | cons w ws ih=>
    cases i with
    | inl i=>
      change WordCursor.cursor v (w++ws.flatten) (finRotate w.length i).val=
        WordCursor.cursor v (w++ws.flatten) i.val*v (w.get i)
      rw [WordCursor.cursor_append_left v _ _ _ (finRotate _ i).isLt.le,
        WordCursor.cursor_append_left v _ _ _ i.isLt.le]
      exact cursor_rotation w (h w (List.mem_cons_self)) i
    | inr i=>
      change WordCursor.cursor v (w++ws.flatten) (w.length+(coordinates ws (BlockBoundary.rotation (lengths ws) i)).val)=
        WordCursor.cursor v (w++ws.flatten) (w.length+(coordinates ws i).val)*v (letter ws i)
      rw [WordCursor.cursor_append_right,WordCursor.cursor_append_right,
        ih (fun w hw=>h w (List.mem_cons_of_mem _ hw)),mul_assoc]
def liftOfDisk (d : WordPairing.Data inv ws.flatten.get) (hd : WordCursor.Paired v inv d)
    (h : ∀w∈ws,WordCursor.value v w=1) : Lift v (ofDisk ws d) where
  position i := WordCursor.cursor v ws.flatten (coordinates ws i).val
  next := flat_rotation ws h
  pair i := by
    change WordCursor.cursor v ws.flatten (coordinates ws ((coordinates ws).symm.permCongr d.partner i)).val=_
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,letter_eq]
    exact hd _
end
end TorsionFreeZeroDivisors.WordBlocks

end



end OAI
