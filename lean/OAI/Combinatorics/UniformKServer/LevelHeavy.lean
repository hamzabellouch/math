import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMap

namespace OAI

                                 
section

noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance heavyPairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance heavyIndexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance heavyTierDecEq : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)

theorem point_at (D : Data X N H) (n : Fin N) : D.point n.val=D.center n := by
  simp only [point,dite_eq_left n.isLt]

theorem heavy_center (D : Data X N H) (n : Fin N) (hh : D.heavy n) (ω : HeavyTape D) :
    ∃ l∈(D.heavyState ω (n.val+1)).present,
      dist (D.center n) ((D.heavyState ω (n.val+1)).center l) ≤ 8*D.r := by
  have ht : D.heavyFlag n.val := ⟨n.isLt,hh⟩
  have hc := HeavySchedule.centers_coverage D.r D.positive.le D.heavyFlag D.point n.val ht
  have he : HeavyRecords.centers (D.heavyState ω (n.val+1))=
      HeavySchedule.centers D.r D.heavyFlag D.point (n.val+1) :=
    HeavyProcess.run_centers D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point
      (HeavyProcess.radiusStream D.r N ω) (HeavyProcess.radiusStream_bounds D.r D.positive.le N ω) (n.val+1)
  rw [←he,point_at] at hc
  obtain ⟨c,hc,hd⟩ := hc
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hc
  exact ⟨l,hl,hd⟩

theorem heavy_agreement (D : Data X N H) (n : Fin N) (hh : D.heavy n)
    (ω : Tape D) (p : X) (hp : dist (D.center n) p ≤ 8*D.r) :
    ∃ l, D.heavyKey ω (n.val+1) (D.center n)=some l ∧ D.heavyKey ω (n.val+1) p=some l := by
  obtain ⟨l,hl,hd⟩ := heavy_center D n hh ω.1
  have hr := ((D.heavyState ω.1 (n.val+1)).radius_bounds l hl).1
  have hc : HeavyRecords.covers (D.heavyState ω.1 (n.val+1)) l (D.center n) := by
    refine ⟨hl,?_⟩
    rw [dist_comm]
    linarith [D.positive]
  have hc' : HeavyRecords.covers (D.heavyState ω.1 (n.val+1)) l p := by
    refine ⟨hl,?_⟩
    have ht := dist_triangle ((D.heavyState ω.1 (n.val+1)).center l) (D.center n) p
    rw [dist_comm _ (D.center n)] at ht
    linarith
  have hs := (HeavyRecords.key_some _ D.positive.le _ l).mpr hc
  have hs' := (HeavyRecords.key_some _ D.positive.le _ l).mpr hc'
  exact ⟨Sum.inl l,by simp only [heavyKey,hs,Option.map_some],by simp only [heavyKey,hs',Option.map_some]⟩

theorem heavy_same_key (D : Data X N H) (is : List (Fin H)) (n : Fin N) (hh : D.heavy n)
    (ω : Tape D) (p : X) (hp : dist (D.center n) p ≤ 8*D.r) :
    D.key is ω (n.val+1) (D.center n)=D.key is ω (n.val+1) p := by
  obtain ⟨l,hx,hp'⟩ := heavy_agreement D n hh ω p hp
  simp only [key,hx,hp',Option.some_or,Option.getD_some]

end UniformKServer.LevelMap.Data

end


end

end OAI
