import Mathlib
import OAI.Algebra.GroupRing.LoopTranspose

namespace OAI



section
namespace TorsionFreeZeroDivisors.HomotopyTracks
open scoped unitInterval
noncomputable section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y} {f : C(X,Y)} (hx : f x=y)
def mapped (p : Path x x) : Path y y := (p.map f.continuous).cast hx.symm hx.symm
variable (H : f.Homotopy (.const _ y)) (hH : ∀t,H (t,x)=y)
def track (p : Path x x) : Path (mapped hx p) (Path.refl y) where
  toFun t := {
    toFun s := H (t,p s)
    continuous_toFun := H.continuous.comp (continuous_const.prodMk p.continuous)
    source' := by rw [p.source];exact hH t
    target' := by rw [p.target];exact hH t }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (H.continuous.comp (continuous_fst.prodMk (p.continuous.comp continuous_snd)))
  source' := by ext s;exact H.apply_zero (p s)
  target' := by ext s;exact H.apply_one (p s)
variable (D : C(X,Path y y)) (hD : D x=Path.refl y)
def run : (ContinuousMap.const X y).Homotopy (.const _ y) where
  toFun z := D z.2 z.1
  continuous_toFun := (Path.continuous_uncurry_iff.mpr D.continuous).comp continuous_swap
  map_zero_left _z := Path.source _
  map_one_left _z := Path.target _
include hD in
lemma run_base (t : unitInterval) : run D (t,x)=y := by
  change D x t=y
  rw [hD];rfl
include hH hD in
lemma trans_base (t : unitInterval) : (H.trans (run D)) (t,x)=y := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact run_base D hD _
lemma track_trans (p : Path x x) :
    track hx (H.trans (run D)) (trans_base H hH D hD) p=
      (track hx H hH p).trans (LoopTranspose.turnPath y ((p.map D.continuous).cast hD.symm hD.symm)) := by
  ext t s
  change (H.trans (run D)) (t,p s)=((track hx H hH p).trans
    (LoopTranspose.turnPath y ((p.map D.continuous).cast hD.symm hD.symm))) t s
  rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
  split_ifs <;> rfl
end
end TorsionFreeZeroDivisors.HomotopyTracks

end



end OAI
