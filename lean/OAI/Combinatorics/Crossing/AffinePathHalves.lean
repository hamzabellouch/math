import OAI.Combinatorics.Crossing.IntervalSegments
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Zarankiewicz

def intervalLeft (t : unitInterval) : unitInterval := ⟨t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
def intervalRight (t : unitInterval) : unitInterval := ⟨(1+t.val)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩

theorem intervalLeft_strictMono : StrictMono intervalLeft := by
  intro s t hst
  change s.val/2 < t.val/2
  exact div_lt_div_of_pos_right hst (by norm_num)

theorem intervalRight_strictMono : StrictMono intervalRight := by
  intro s t hst
  change (1+s.val)/2 < (1+t.val)/2
  have hh : s.val < t.val := hst
  linarith

theorem intervalSegment_left (a b t : unitInterval) :
    intervalSegment (intervalLeft a) (intervalLeft b) t=intervalLeft (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*(a.val/2)+t.val*(b.val/2)=((1-t.val)*a.val+t.val*b.val)/2
  ring

theorem intervalSegment_right (a b t : unitInterval) :
    intervalSegment (intervalRight a) (intervalRight b) t=intervalRight (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*((1+a.val)/2)+t.val*((1+b.val)/2)=(1+((1-t.val)*a.val+t.val*b.val))/2
  ring

theorem path_trans_intervalLeft {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalLeft t)=γ t := by
  rw [← (γ.trans η).extend_extends' (intervalLeft t)]
  rw [Path.extend_trans_of_le_half γ η (show (intervalLeft t).val ≤ 1/2 by
    change t.val/2 ≤ 1/2
    linarith [t.property.2])]
  have he : 2*(intervalLeft t).val=t.val := by change 2*(t.val/2)=t.val; ring
  rw [he,γ.extend_extends']

theorem path_trans_intervalRight {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalRight t)=η t := by
  rw [← (γ.trans η).extend_extends' (intervalRight t)]
  rw [Path.extend_trans_of_half_le γ η (show 1/2 ≤ (intervalRight t).val by
    change 1/2 ≤ (1+t.val)/2
    linarith [t.property.1])]
  have he : 2*(intervalRight t).val-1=t.val := by change 2*((1+t.val)/2)-1=t.val; ring
  rw [he,η.extend_extends']

theorem intervalSegment_zero_one (t : unitInterval) : intervalSegment 0 1 t=t := by
  apply Subtype.ext
  change (1-t.val)*0+t.val*1=t.val
  ring

end Zarankiewicz

end

end OAI
