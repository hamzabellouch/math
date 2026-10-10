import Mathlib
import OAI.Combinatorics.UniformKServer.LevelHeavy
import OAI.Combinatorics.UniformKServer.FirstEdits
import OAI.Combinatorics.UniformKServer.HeavyProcessEdits

namespace OAI

noncomputable section

/-! Heavy key edits on the actual tape, with a tape-independent auxiliary ramp. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqHeavyEdit : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqHeavyEdit : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqHeavyEdit : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def heavyPotential (D : Data X N H) (t : ℕ) (p : X) : ℝ :=
  HeavyEditRamp.parameter D.r (HeavySchedule.centers D.r D.heavyFlag D.point t) p

def heavyTrigger (D : Data X N H) (n : Fin N) : Prop :=
  HeavySchedule.trigger D.r (D.heavyFlag n.val)
    (HeavySchedule.centers D.r D.heavyFlag D.point n.val) (D.point n.val)

def heavyEdit (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) : ℝ :=
  indicator (D.heavyKey ω n.val p) (D.heavyKey ω (n.val+1) p)

theorem heavyEdit_le (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) :
    D.r*D.heavyEdit n p ω≤HeavyRecords.editCharge (D.heavyState ω.1 n.val) (D.heavyState ω.1 (n.val+1)) p := by
  have h := mul_le_mul_of_nonneg_left (indicator_map (Option.map (Sum.inl : HeavySlot X→Label D))
    (HeavyRecords.key (D.heavyState ω.1 n.val) p) (HeavyRecords.key (D.heavyState ω.1 (n.val+1)) p)) D.positive.le
  change D.r*D.heavyEdit n p ω≤_ at h
  apply h.trans_eq
  unfold indicator HeavyRecords.editCharge
  split_ifs <;> simp_all

theorem heavyFlag_at (D : Data X N H) (n : Fin N) : D.heavyFlag n.val↔D.heavy n := by
  constructor
  · rintro ⟨_,hh⟩; exact hh
  · exact fun h=>⟨n.isLt,h⟩

theorem heavy_stationary (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) :
    D.r*(D.heavyEdit n p ω+D.heavyPotential (n.val+1) p-D.heavyPotential n.val p)≤
      if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p ∧ dist (D.center n) p≤120*D.r then 2*D.r else 0 := by
  have h := HeavyProcess.run_stationary_payment D.base D.positive
    (show 2*Fintype.card X<Fintype.card (HeavySlot X) by simp [HeavySlot])
    D.heavyFlag D.point (HeavyProcess.radiusStream D.r N ω.1)
    (HeavyProcess.radiusStream_bounds D.r D.positive.le N ω.1) n.val p
  change HeavyRecords.editCharge (D.heavyState ω.1 n.val) (D.heavyState ω.1 (n.val+1)) p+
    D.r*(D.heavyPotential (n.val+1) p-D.heavyPotential n.val p)≤
      (if D.heavyTrigger n ∧ 3*D.r<dist p (D.point n.val) ∧ dist p (D.point n.val)≤120*D.r then 2*D.r else 0) at h
  rw [point_at,dist_comm p] at h
  nlinarith only [h,D.heavyEdit_le n p ω]

theorem heavy_mover (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) :
    D.r*(D.heavyEdit n p ω+D.heavyPotential (n.val+1) (D.center n)-D.heavyPotential n.val p)≤
      (if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p then D.r else 0)+
        (if D.heavy n then 0 else dist (D.center n) p) := by
  have h := HeavyProcess.run_mover_payment D.base D.positive
    (show 2*Fintype.card X<Fintype.card (HeavySlot X) by simp [HeavySlot])
    D.heavyFlag D.point (HeavyProcess.radiusStream D.r N ω.1)
    (HeavyProcess.radiusStream_bounds D.r D.positive.le N ω.1) n.val p
  change HeavyRecords.editCharge (D.heavyState ω.1 n.val) (D.heavyState ω.1 (n.val+1)) p+
    D.r*(D.heavyPotential (n.val+1) (D.point n.val)-D.heavyPotential n.val p)≤
      (if D.heavyTrigger n ∧ 3*D.r<dist p (D.point n.val) then D.r else 0)+
        (if D.heavyFlag n.val then 0 else dist (D.point n.val) p) at h
  rw [point_at,dist_comm p,heavyFlag_at] at h
  nlinarith only [h,D.heavyEdit_le n p ω]

end UniformKServer.LevelMap.Data

end

end OAI
