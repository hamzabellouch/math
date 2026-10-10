import OAI.Combinatorics.Crossing.IntervalSegments
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intervalSegment_injective (a b : unitInterval) (hab : a < b) :
    Function.Injective (intervalSegment a b) := by
  intro s t he
  have hh := congrArg Subtype.val he
  have hpos : 0 < b.val-a.val := sub_pos.mpr hab
  apply Subtype.ext
  change (1-s.val)*a.val+s.val*b.val=(1-t.val)*a.val+t.val*b.val at hh
  have hz : (s.val-t.val)*(b.val-a.val)=0 := by nlinarith [hh]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos))

theorem intervalSegment_surjective_interval (a b : unitInterval) (hab : a < b)
    (t : unitInterval) (ht : a ≤ t ∧ t ≤ b) : ∃ u : unitInterval, intervalSegment a b u=t := by
  have hd : 0 < b.val-a.val := sub_pos.mpr hab
  have ht0 : 0 ≤ (t.val-a.val)/(b.val-a.val) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have ht1 : (t.val-a.val)/(b.val-a.val) ≤ 1 :=
    (div_le_one hd).mpr (sub_le_sub_right (show t.val ≤ b.val from ht.2) a.val)
  refine ⟨⟨(t.val-a.val)/(b.val-a.val),ht0,ht1⟩,?_⟩
  apply Subtype.ext
  change (1-(t.val-a.val)/(b.val-a.val))*a.val+((t.val-a.val)/(b.val-a.val))*b.val=t.val
  field_simp
  ring

def pathSubarc {a b : Plane} (γ : Path a b) (u v : unitInterval) : Path (γ u) (γ v) where
  toFun := fun t => γ (intervalSegment u v t)
  continuous_toFun := by
    apply γ.continuous.comp
    unfold intervalSegment
    fun_prop
  source' := by simp [intervalSegment]
  target' := by simp [intervalSegment]

theorem pathSubarc_injective {a b : Plane} (γ : Path a b) (hγ : Function.Injective γ)
    (u v : unitInterval) (huv : u < v) : Function.Injective (pathSubarc γ u v) :=
  hγ.comp (intervalSegment_injective u v huv)

theorem pathSubarc_range {a b : Plane} (γ : Path a b) (u v : unitInterval) (huv : u < v) :
    Set.range (pathSubarc γ u v)=γ '' Set.Icc u v := by
  apply Set.Subset.antisymm
  · rintro x ⟨t,rfl⟩
    exact ⟨intervalSegment u v t,intervalSegment_between u v t huv.le,rfl⟩
  · rintro x ⟨t,ht,rfl⟩
    obtain ⟨s,hs⟩ := intervalSegment_surjective_interval u v huv t ht
    exact ⟨s,congrArg γ hs⟩

end Zarankiewicz

end

end OAI
