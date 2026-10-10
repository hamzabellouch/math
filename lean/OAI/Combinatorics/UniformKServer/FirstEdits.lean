import Mathlib
import OAI.Combinatorics.UniformKServer.FirstStructure
import OAI.Combinatorics.UniformKServer.KeyEdits

namespace OAI

                                 
section

/-! Serializing actual priority edits. The higher-priority prefix uses its
new state and the lower-priority suffix its old state, exactly as in source. -/
noncomputable section
namespace UniformKServer.FirstStructure
open scoped Classical
variable {I J : Type*}

def overlayKey (e : Option J) (is : List I) (f : I→Option J) (z : J) : J :=
  (e.or (first is f)).getD z

def editSum (f g : I→Option J) (z : J) : Option J→List I→ℝ
  | _,[] => 0
  | e,i::is => KeyEdits.changed e id ((first is f).getD z) (f i) (g i)+
      editSum f g z (e.or (g i)) is

theorem indicator_triangle (a b c : J) : indicator a c ≤ indicator a b+indicator b c := by
  unfold indicator
  split_ifs <;> simp_all

theorem overlay_step (e : Option J) (b : Option J) (is : List I) (f : I→Option J) (z : J) :
    (e.or (b.or (first is f))).getD z=KeyEdits.overlay e id ((first is f).getD z) b := by
  cases e <;> cases b <;> rfl

theorem serial_bound (e : Option J) (is : List I) (f g : I→Option J) (z : J) :
    indicator (overlayKey e is f z) (overlayKey e is g z)≤editSum f g z e is := by
  induction is generalizing e with
  | nil => simp [overlayKey,first,indicator,editSum]
  | cons i is ih =>
    have h := indicator_triangle (overlayKey e (i::is) f z)
      (overlayKey (e.or (g i)) is f z) (overlayKey e (i::is) g z)
    have h1 : indicator (overlayKey e (i::is) f z) (overlayKey (e.or (g i)) is f z)=
        KeyEdits.changed e id ((first is f).getD z) (f i) (g i) := by
      simp only [overlayKey,first]
      have he : ((e.or (g i)).or (first is f)).getD z=(e.or ((g i).or (first is f))).getD z := by
        cases e <;> rfl
      rw [he,overlay_step,overlay_step]
      rfl
    have h2 : overlayKey e (i::is) g z=overlayKey (e.or (g i)) is g z := by
      cases e <;> rfl
    rw [h1,h2] at h
    rw [h2]
    exact h.trans (add_le_add le_rfl (ih (e.or (g i))))

theorem editSum_nonneg (e : Option J) (is : List I) (f g : I→Option J) (z : J) :
    0≤editSum f g z e is := by
  induction is generalizing e with
  | nil => rfl
  | cons i is ih => exact add_nonneg (KeyEdits.changed_bounds _ _ _ _ _).1 (ih _)

end UniformKServer.FirstStructure

end


end

end OAI
