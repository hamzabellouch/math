import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCover

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

/-- Prefix coordinates really close at the last side. This uses the entire
cell relation, including the wraparound endpoint, not a weakened path equation. -/
lemma group_prefix_rotate {G : Type*} [Group G] {m : ℕ} (p : Fin m → G)
    (hp : (List.ofFn p).prod = 1) (i : Fin m) :
    ((List.ofFn p).take ((finRotate m i).val)).prod =
      ((List.ofFn p).take i.val).prod * p i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hs := List.prod_take_succ (List.ofFn p) i.val (by simpa only [List.length_ofFn] using i.isLt)
    have he : (List.ofFn p)[i.val] = p i := List.getElem_ofFn (by simpa only [List.length_ofFn] using i.isLt)
    rw [he] at hs
    by_cases hi : i = Fin.last m
    · subst i
      rw [finRotate_apply,Fin.val_add_one,ite_eq_left rfl]
      have hlen : (Fin.last m).val + 1 = (List.ofFn p).length := by simp only [Fin.val_last,List.length_ofFn]
      rw [hlen,List.take_length,hp] at hs
      simpa only [List.take_zero,List.prod_nil] using hs
    · rw [finRotate_apply,Fin.val_add_one,ite_eq_right hi]
      exact hs

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
include hv hcell in
lemma frozenOffset_next (s : (frozenBoundary n w d).Side) :
    frozenOffset n w d v ((frozenBoundary n w d).next s) =
      frozenOffset n w d v s * v ((frozenBoundary n w d).sideLabel s) := by
  have hprefix (a : FrozenCell n w d) (i : Fin ((frozenBoundary n w d).size a)) :
      (((List.ofFn ((frozenBoundary n w d).label a)).take ((finRotate _ i).val)).map v).prod =
        (((List.ofFn ((frozenBoundary n w d).label a)).take i.val).map v).prod *
          v ((frozenBoundary n w d).label a i) := by
    simp only [List.map_take,List.map_ofFn]
    exact group_prefix_rotate (fun i => v ((frozenBoundary n w d).label a i))
      (hcell (frozenCell n w d a)) i
  rcases s with ⟨a,b,i⟩
  cases b with
  | false =>
    change _ = (_ * v ((frozenBoundary n w d).label a i)) * v (rev n w ((frozenBoundary n w d).label a i))
    rw [hv,mul_inv_cancel_right]
    change (((List.ofFn ((frozenBoundary n w d).label a)).take (((finRotate _)⁻¹ i).val)).map v).prod *
      v ((frozenBoundary n w d).label a ((finRotate _)⁻¹ i)) = _
    simpa only [Perm.inv_def,Equiv.apply_symm_apply] using (hprefix a ((finRotate _)⁻¹ i)).symm
  | true => exact hprefix a i

/-- Every indexed frozen face has its genuine closed lifted boundary, so the
cover's closed-walk condition does not discard any actual lifted cell. -/
lemma actualCellCover_frozen_closed (g : G) (s : (frozenBoundary n w d).Side) :
    let H := actualCellCover n w d v hv hcell
    let T := H.target (fun _ _ => (0 : ℤ)) (by simp)
    T.front (g,Sum.inr ((frozenBoundary n w d).next s)) =
      T.back (g,Sum.inr s) := by
  apply Prod.ext
  · change g * frozenOffset n w d v ((frozenBoundary n w d).next s) =
      g * frozenOffset n w d v ((frozenBoundary n w d).opposite s)
    rw [frozenOffset_next n w d v hv hcell,frozenOffset_opposite n w d v hv]
  · exact congrArg Sum.inr ((frozenBoundary n w d).next_start s)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
