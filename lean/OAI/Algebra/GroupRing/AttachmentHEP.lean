import Mathlib
import OAI.Algebra.GroupRing.HomotopyFunctor
import OAI.Algebra.GroupRing.CellHEP

namespace OAI



section
namespace TorsionFreeZeroDivisors.AttachmentHEP
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
universe u v w
variable {X : Type u} {Y : Type v} {J : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {n : ℕ} (a : J→C(Sphere n,X)) (f : C(Space a,Y))
  (H : C(unitInterval × X,Y)) (h : ∀x,H (0,x)=f (base a x))
def eval (t : unitInterval) : C(C(unitInterval,Y),Y) := ⟨fun p=>p t,continuous_eval_const t⟩
def basePaths : C(X,C(unitInterval,Y)) := H.comp ⟨Prod.swap,continuous_swap⟩ |>.curry
def cellPaths (i : J) : C(Disk n,C(unitInterval,Y)) :=
  ((CellHEP.extension (f.comp (cell a i))
    (H.comp ⟨fun z : unitInterval × Sphere n=>(z.1,a i z.2),
      continuous_fst.prodMk ((a i).continuous.comp continuous_snd)⟩)
    (fun x=>by change H (0,a i x)=f (cell a i (boundary n x));rw [h,cell_boundary])).comp
      ⟨Prod.swap,continuous_swap⟩).curry
lemma cellPaths_boundary (i : J) (x : Sphere n) :
    cellPaths a f H h i (boundary n x)=basePaths H (a i x) := by
  apply ContinuousMap.ext
  intro t
  dsimp only [cellPaths,basePaths,ContinuousMap.curry_apply,ContinuousMap.comp_apply,ContinuousMap.coe_mk,Prod.swap]
  change CellHEP.extension _ _ _ (t,Cellular.boundary n x)=_
  rw [CellHEP.extension_boundary]
  rfl
lemma cellPaths_zero (i : J) (d : Disk n) : cellPaths a f H h i d 0=f (cell a i d) := by
  dsimp only [cellPaths,ContinuousMap.curry_apply,ContinuousMap.comp_apply,ContinuousMap.coe_mk,Prod.swap]
  rw [CellHEP.extension_zero]
  rfl
def paths : C(Space a,C(unitInterval,Y)) :=
  lift a (basePaths H) (cellPaths a f H h) (cellPaths_boundary a f H h)
lemma paths_base (x : X) (t : unitInterval) : paths a f H h (base a x) t=H (t,x) := rfl
lemma paths_zero (x : Space a) : paths a f H h x 0=f x := by
  have he : (eval 0).comp (paths a f H h)=f := by
    apply lift_unique a
    · intro x
      exact h x
    · intro i d
      change paths a f H h (cell a i d) 0=f (cell a i d)
      rw [paths,lift_cell]
      exact cellPaths_zero a f H h i d
  exact ContinuousMap.congr_fun he x
/-- Homotopy extension for a genuine disk attachment with arbitrarily many
cells. Currying into the compact-open path space respects the weak topology. -/
def extend : C(unitInterval × Space a,Y) := (paths a f H h).uncurry.comp ⟨Prod.swap,continuous_swap⟩
lemma extend_base (t : unitInterval) (x : X) : extend a f H h (t,base a x)=H (t,x) := rfl
lemma extend_zero (x : Space a) : extend a f H h (0,x)=f x := paths_zero a f H h x
def endpoint : C(Space a,Y) := (eval 1).comp (paths a f H h)
def homotopy : f.Homotopy (endpoint a f H h) where
  toContinuousMap := extend a f H h
  map_zero_left := extend_zero a f H h
  map_one_left _ := rfl
lemma endpoint_base (x : X) : endpoint a f H h (base a x)=H (1,x) := rfl
end
end TorsionFreeZeroDivisors.AttachmentHEP

end



end OAI
