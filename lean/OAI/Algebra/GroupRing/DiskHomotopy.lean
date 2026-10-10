import Mathlib
import OAI.Algebra.GroupRing.DiskTracks
import OAI.Algebra.GroupRing.HomotopyTracks

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DiskTracks
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open GroupRingTopology.Cellular hiding Disk Sphere boundary
open scoped unitInterval
variable {Y : Type} [TopologicalSpace Y] {y : Y} {p : Path y y}
  {c h : Path p (Path.refl y)}
def squareHomotopy (H : c.Homotopy h) : (square c).Homotopy (square h) where
  toFun z := square (H.eval z.1) z.2
  continuous_toFun := (Path.continuous_uncurry_iff.mpr H.continuous).comp
    ((continuous_fst.prodMk (continuous_diskTime.comp continuous_snd)).prodMk
      (Cayley.continuous_edgeTime.comp (continuous_diskTail.comp continuous_snd)))
  map_zero_left d := by
    change H (0,diskTime d) _=c _ _
    rw [H.apply_zero];rfl
  map_one_left d := by
    change H (1,diskTime d) _=h _ _
    rw [H.apply_one];rfl
lemma squareHomotopy_boundary (H : c.Homotopy h) (t : unitInterval) (z : Sphere 2) :
    squareHomotopy H (t,boundary 2 z)=LoopSphere.map p z := square_boundary (H.eval t) z

def extension (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)
    (h : Path p (Path.refl y)) (H : (physical F hF).Homotopy h) : F.Homotopy (.const _ y) := by
  have e := (squareHomotopy H).trans (contract h)
  exact { e with
    map_zero_left := fun d=>(e.apply_zero d).trans (ContinuousMap.congr_fun (square_physical F hF) d) }
lemma extension_boundary (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)
    (h : Path p (Path.refl y)) (H : (physical F hF).Homotopy h)
    (t : unitInterval) (z : Sphere 2) :
    extension F hF h H (t,boundary 2 z)=
      if ht : (t:ℝ)≤1/2 then LoopSphere.map p z
      else LoopSphere.map (h ⟨2*t-1,unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le,t.2.2⟩⟩) z := by
  change ((squareHomotopy H).trans (contract h)) (t,boundary 2 z)=_
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact squareHomotopy_boundary H _ z
  · exact contract_boundary h _ z
end TorsionFreeZeroDivisors.DiskTracks
namespace TorsionFreeZeroDivisors.HomotopyTracks
open GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} {f : C(X,Y)} (hx : f x=y)
lemma natural_cast (p : Path x x) : LoopSphere.map (mapped hx p)=f.comp (LoopSphere.map p) := by
  subst y
  exact LoopSphere.natural p f
variable (H : f.Homotopy (.const _ y)) (hH : ∀t,H (t,x)=y)
lemma track_boundary (p : Path x x) (t : unitInterval) (z : Sphere 2) :
    LoopSphere.map ((track hx H hH p) t) z=H (t,LoopSphere.map p z) := by
  let k : C(X,Y) := ⟨fun u=>H (t,u),H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact ContinuousMap.congr_fun (natural_cast (f:=k) (hH t) p) z
end TorsionFreeZeroDivisors.HomotopyTracks

end

end OAI
