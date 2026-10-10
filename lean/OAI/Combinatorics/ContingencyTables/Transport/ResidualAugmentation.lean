import OAI.Combinatorics.ContingencyTables.Transport.ResidualSearch
import OAI.Combinatorics.ContingencyTables.Transport.PathAugmentation
import Mathlib.Data.List.MinMax

namespace OAI

/-! # Executed bottleneck and residual augmentation

The program takes the actual BFS path list, scans its residual capacities
for a minimum, and adds the resulting skew path flow. No path or amount
is chosen through a mathematical existence proof.
-/

namespace ContingencyTables.ResidualAugmentation

open PublishedEdmondsKarp
open scoped BigOperators

variable {n : ℕ}

def arcs : List (Fin n) → List (Fin n×Fin n)
  | [] => []
  | [_] => []
  | u::v::xs => (u,v)::arcs (v::xs)

def bottleneck (c : Capacity n) (f : Flow n) (xs : List (Fin n)) : ℤ :=
  ((arcs xs).map (fun uv=>(c uv.1 uv.2:ℤ)-f uv.1 uv.2)).min?.getD 0

def listUpdate (f : Flow n) (xs : List (Fin n)) (a : ℤ) : Flow n :=
  fun u v=>f u v+a*((((arcs xs).map (fun uv=>if uv=(u,v) then (1:ℤ) else 0)).sum)-
    (((arcs xs).map (fun uv=>if uv=(v,u) then (1:ℤ) else 0)).sum))

def step (c : Capacity n) (s t : Fin n) (f : Flow n) : Option (Flow n) :=
  (ResidualSearch.search c f s t).map (fun xs=>listUpdate f xs (bottleneck c f xs))

lemma arcs_ofFn (k : ℕ) (p : Fin (k+1) → Fin n) :
    arcs (List.ofFn p)=List.ofFn (fun i : Fin k=>(p i.castSucc,p i.succ)) := by
  induction k with
  | zero => simp [List.ofFn_succ,arcs]
  | succ k ih =>
    rw [List.ofFn_succ (f:=p)]
    rw [List.ofFn_succ (f:=fun i : Fin (k+1)=>p i.succ)]
    rw [arcs]
    have h := ih (fun i : Fin (k+1)=>p i.succ)
    rw [List.ofFn_succ] at h
    rw [h,List.ofFn_succ]
    rfl

lemma listUpdate_ofFn (f : Flow n) (k : ℕ) (p : Fin (k+1) → Fin n) (a : ℤ) :
    listUpdate f (List.ofFn p) a=PathAugmentation.update f p a := by
  funext u v
  simp only [listUpdate,arcs_ofFn,List.map_ofFn,Function.comp_apply,Fin.sum_ofFn,
    PathAugmentation.update,PathAugmentation.arcCount,Prod.mk.injEq]

lemma bottleneck_ofFn (c : Capacity n) (f : Flow n) (k : ℕ)
    (p : Fin (k+1) → Fin n) :
    bottleneck c f (List.ofFn p)=
      (List.ofFn (fun i : Fin k=>(c (p i.castSucc) (p i.succ):ℤ)-
        f (p i.castSucc) (p i.succ))).min?.getD 0 := by
  simp only [bottleneck,arcs_ofFn,List.map_ofFn,Function.comp_def]

lemma bottleneck_spec (c : Capacity n) (s t : Fin n) (hst : s≠t) (f : Flow n)
    (k : ℕ) (p : Fin (k+1) → Fin n) (hp : ResidualPath c f s t k p) :
    0<bottleneck c f (List.ofFn p) ∧
    (∀ i : Fin k,bottleneck c f (List.ofFn p)≤
      (c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) ∧
    ∃ i : Fin k,bottleneck c f (List.ofFn p)=
      (c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ) := by
  have hk : k≠0 := by
    intro h
    subst k
    have he : s=t := hp.1.symm.trans hp.2.1
    exact hst he
  let r : Fin k → ℤ := fun i=>(c (p i.castSucc) (p i.succ):ℤ)-
    f (p i.castSucc) (p i.succ)
  rw [bottleneck_ofFn]
  change 0<(List.ofFn r).min?.getD 0 ∧
    (∀ i,(List.ofFn r).min?.getD 0≤r i) ∧ ∃ i,(List.ofFn r).min?.getD 0=r i
  cases hm : (List.ofFn r).min? with
  | none =>
    have hz : k=0 := List.ofFn_eq_nil_iff.mp (List.min?_eq_none_iff.mp hm)
    exact False.elim (hk hz)
  | some a =>
    have ha := List.min?_eq_some_iff.mp hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ha.1
    simp only [Option.getD_some]
    refine ⟨?_,?_,⟨i,hi.symm⟩⟩
    · rw [←hi]
      exact hp.2.2.2 i
    · intro j
      exact ha.2 (r j) (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem step_augmentation (c : Capacity n) (s t : Fin n) (hst : s≠t)
    (f g : Flow n) (h : step c s t f=some g) : ShortestAugmentation c s t f g := by
  obtain ⟨xs,hxs,hg⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨k,p,hp,hr,hshort⟩ := ResidualSearch.search_shortest c f s t xs hxs
  subst xs
  have hb := bottleneck_spec c s t hst f k p hr
  refine ⟨k,p,bottleneck c f (List.ofFn p),hr,hshort,hb.1,hb.2.1,hb.2.2,?_⟩
  intro u v
  rw [←hg,listUpdate_ofFn]
  rfl

theorem step_feasible (c : Capacity n) (s t : Fin n) (hst : s≠t)
    (f g : Flow n) (hf : Feasible c s t f) (h : step c s t f=some g) :
    Feasible c s t g := by
  obtain ⟨k,p,a,hp,_,ha,hr,_,hu⟩ := step_augmentation c s t hst f g h
  have he : g=PathAugmentation.update f p a := funext (fun u=>funext (hu u))
  rw [he]
  exact PathAugmentation.update_feasible c s t f hf p hp a ha.le hr

theorem step_none_maximum (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (h : step c s t f=none) : IsMaximum c s t f := by
  apply ResidualSearch.failure_maximum c s t f hf
  exact Option.map_eq_none_iff.mp h

end ContingencyTables.ResidualAugmentation

end OAI
