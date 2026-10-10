import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenNetwork
import OAI.Combinatorics.PolynomialVacuum.Cylinder.WordArray

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
namespace OpenNetwork
variable {M : ℕ} (C : OpenNetwork M)

private theorem exists_turn (i o : Fin 3) (h : i≠o) :
    ∃b : Bool,i+(if b then 2 else 1)=o := by
  fin_cases i <;> fin_cases o
  all_goals first | exact (h rfl).elim | decide

noncomputable def turn (v : C.sites) : Bool := (exists_turn (C.enter v) (C.exit v) (C.distinct v)).choose

theorem outgoing_turn (v : C.sites) : outgoingSlot (v.val,C.enter v) (C.turn v)=C.exit v :=
  (exists_turn (C.enter v) (C.exit v) (C.distinct v)).choose_spec

noncomputable def pathLast (a : C.sites) (ha : C.Source a) : Fin (C.pathLength a ha) :=
  ⟨C.pathLength a ha-1,by have := C.pathLength_pos a ha; omega⟩

noncomputable def pathEnd (a : C.sites) (ha : C.Source a) : Germ M :=
  let v:=C.pathSite a ha (C.pathLast a ha)
  (neighbor v.val (C.exit v),C.exit v)

noncomputable def pathGerm (a : C.sites) (ha : C.Source a) (j : Fin (C.pathLength a ha+1)) : Germ M :=
  if hj : j.val<C.pathLength a ha then
    ((C.pathSite a ha ⟨j.val,hj⟩).val,C.enter (C.pathSite a ha ⟨j.val,hj⟩)) else C.pathEnd a ha

@[simp] theorem pathGerm_cast (a : C.sites) (ha : C.Source a) (j : Fin (C.pathLength a ha)) :
    C.pathGerm a ha j.castSucc=((C.pathSite a ha j).val,C.enter (C.pathSite a ha j)) := by
  simp [pathGerm,j.isLt]
@[simp] theorem pathGerm_last (a : C.sites) (ha : C.Source a) :
    C.pathGerm a ha (Fin.last (C.pathLength a ha))=C.pathEnd a ha := by simp [pathGerm]
@[simp] theorem pathGerm_start (a : C.sites) (ha : C.Source a) :
    C.pathGerm a ha 0=(a.val,C.enter a) := by
  simp [pathGerm,C.pathLength_pos a ha,C.pathSite_start]

theorem pathGerm_step (a : C.sites) (ha : C.Source a) (j : Fin (C.pathLength a ha)) :
    advance (C.pathGerm a ha j.castSucc) (C.turn (C.pathSite a ha j))=C.pathGerm a ha j.succ := by
  rw [C.pathGerm_cast]
  change (neighbor (C.pathSite a ha j).val (outgoingSlot _ _),outgoingSlot _ _)=_
  rw [C.outgoing_turn]
  by_cases hj : j.val+1<C.pathLength a ha
  · let k : Fin (C.pathLength a ha):=⟨j.val+1,hj⟩
    have hn:=C.pathSite_next a ha j k rfl
    have hm:=C.matching (C.pathSite a ha j) (C.pathSite a ha k) hn
    simp only [pathGerm,Fin.val_succ,hj,dite_true]
    exact Prod.ext hn hm.symm
  · have he : j=C.pathLast a ha := by
      apply Fin.ext
      have hn:=j.isLt
      change j.val=C.pathLength a ha-1
      omega
    simp only [pathGerm,Fin.val_succ,hj,dite_false]
    rw [he]
    rfl

noncomputable def pathWord (a : C.sites) (ha : C.Source a) : List Bool :=
  List.ofFn (fun j => C.turn (C.pathSite a ha j))

theorem pathWord_trace (a : C.sites) (ha : C.Source a) :
    traced (a.val,C.enter a) (C.pathWord a ha)=List.ofFn (fun j => (C.pathSite a ha j).val) := by
  have h:= (wordArray_trace (C.pathGerm a ha) (fun j => C.turn (C.pathSite a ha j))
    (C.pathGerm_step a ha)).1
  simpa [pathWord] using h

theorem pathWord_terminal (a : C.sites) (ha : C.Source a) :
    terminalGerm (a.val,C.enter a) (C.pathWord a ha)=C.pathEnd a ha := by
  have h:= (wordArray_trace (C.pathGerm a ha) (fun j => C.turn (C.pathSite a ha j))
    (C.pathGerm_step a ha)).2
  simpa [pathWord] using h

theorem pathWord_nodup (a : C.sites) (ha : C.Source a) :
    (traced (a.val,C.enter a) (C.pathWord a ha)).Nodup := by
  rw [C.pathWord_trace]
  exact List.nodup_ofFn.mpr (Subtype.val_injective.comp (C.pathSite_injective a ha))

theorem pathWord_inside (a : C.sites) (ha : C.Source a) {v : Vertex M}
    (hv : v∈traced (a.val,C.enter a) (C.pathWord a ha)) : v∈C.sites := by
  rw [C.pathWord_trace,List.mem_ofFn] at hv
  obtain ⟨j,rfl⟩:=hv
  exact (C.pathSite a ha j).property

theorem pathWord_outside (a : C.sites) (ha : C.Source a) :
    (terminalGerm (a.val,C.enter a) (C.pathWord a ha)).1∉C.sites := by
  rw [C.pathWord_terminal]
  apply C.pathSite_exit a ha (C.pathLast a ha)
  change C.pathLength a ha-1+1=C.pathLength a ha
  have := C.pathLength_pos a ha
  omega
end OpenNetwork
end PolynomialVacuumCylinder

end OAI
