import OAI.Combinatorics.ContingencyTables.Transport.FiniteDirectedBFS
import OAI.Combinatorics.ContingencyTables.Transport.PublishedEdmondsKarp
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-! # The computed residual search and its maximum-flow certificate

The search itself is the deterministic directed BFS. Success supplies
the precise shortest simple residual path required by the published
augmentation bound; failure supplies a saturated cut, hence maximality.
-/

namespace ContingencyTables.ResidualSearch

open FiniteDirectedBFS PublishedEdmondsKarp
open scoped BigOperators

variable {n : ℕ}

def edge (c : Capacity n) (f : Flow n) (u v : Fin n) : Bool :=
  decide (0<(c u v:ℤ)-f u v)

def search (c : Capacity n) (f : Flow n) (s t : Fin n) : Option (List (Fin n)) :=
  paths (edge c f) s n t

lemma route_of_fin (E : Fin n → Fin n → Bool) (k : ℕ)
    (p : Fin (k+1) → Fin n)
    (hp : ∀ i : Fin k,E (p i.castSucc) (p i.succ)=true) :
    Route E (p 0) (p (Fin.last k)) (List.ofFn p) := by
  induction k with
  | zero => simpa [List.ofFn_succ] using (Route.start (E:=E) (s:=p 0))
  | succ k ih =>
    let q : Fin (k+1) → Fin n := fun i=>p i.castSucc
    have hq : ∀ i : Fin k,E (q i.castSucc) (q i.succ)=true := by
      intro i
      exact hp i.castSucc
    have hr := ih q hq
    have he : E (q (Fin.last k)) (p (Fin.last (k+1)))=true :=
      hp (Fin.last k)
    simpa only [List.ofFn_succ_last,q,Fin.castSucc_zero] using hr.extend he

lemma route_of_residual (c : Capacity n) (f : Flow n) (s t : Fin n)
    (k : ℕ) (p : Fin (k+1) → Fin n) (hp : ResidualPath c f s t k p) :
    Route (edge c f) s t (List.ofFn p) := by
  have h := route_of_fin (edge c f) k p (fun i=>by simpa [edge] using hp.2.2.2 i)
  simpa only [hp.1,hp.2.1] using h

theorem search_shortest (c : Capacity n) (f : Flow n) (s t : Fin n)
    (xs : List (Fin n)) (hs : search c f s t=some xs) :
    ∃ (k : ℕ) (p : Fin (k+1) → Fin n),
      xs=List.ofFn p ∧ ResidualPath c f s t k p ∧
      ∀ (l : ℕ) (q : Fin (l+1) → Fin n), ResidualPath c f s t l q → k≤l := by
  have hr := (paths_sound hs).1
  have hn := paths_nodup hs
  cases xs with
  | nil => exact False.elim (hr.nonempty rfl)
  | cons a ys =>
    let p : Fin (ys.length+1) → Fin n := Fin.cons a ys.get
    have he : List.ofFn p=a::ys := by simp [p]
    have hhead : p 0=s := by simpa [←he,List.ofFn_succ] using hr.head
    have hlast : p (Fin.last ys.length)=t := by
      have hh := hr.last
      rw [←he,List.getLast?_eq_some_getLast (by simp)] at hh
      simpa only [List.getLast_ofFn_succ,Option.some.injEq] using hh
    have hinj : Function.Injective p := List.nodup_ofFn.mp (he.symm ▸ hn)
    have hchain := List.isChain_ofFn.mp (he.symm ▸ hr.chain)
    have hres : ResidualPath c f s t ys.length p := by
      refine ⟨hhead,hlast,hinj,?_⟩
      intro i
      have hc := hchain i.val (by omega)
      change edge c f (p i.castSucc) (p i.succ)=true at hc
      exact of_decide_eq_true hc
    refine ⟨ys.length,p,he.symm,hres,?_⟩
    intro l q hq
    have hle := paths_shortest hs (List.ofFn q) (route_of_residual c f s t l q hq)
    simpa using hle

def reached (c : Capacity n) (f : Flow n) (s : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v=>(paths (edge c f) s n v).isSome)

lemma mem_reached (c : Capacity n) (f : Flow n) (s v : Fin n) :
    v∈reached c f s ↔ discovered (paths (edge c f) s n) v := by
  simp [reached,discovered,Option.isSome_iff_exists]

lemma source_reached (c : Capacity n) (f : Flow n) (s : Fin n) :
    s∈reached c f s := (mem_reached c f s s).mpr (source_found _ _)

lemma target_not_reached (c : Capacity n) (f : Flow n) (s t : Fin n)
    (h : search c f s t=none) : t∉reached c f s := by
  rw [mem_reached]
  rintro ⟨xs,hxs⟩
  simp [search] at h
  simp [h] at hxs

lemma cut_saturated (c : Capacity n) (f : Flow n) (s : Fin n)
    (hcap : ∀ u v,f u v≤c u v) {u v : Fin n}
    (hu : u∈reached c f s) (hv : v∉reached c f s) : f u v=c u v := by
  have hno : ¬0<(c u v:ℤ)-f u v := by
    intro hp
    have he : edge c f u v=true := by simpa [edge] using hp
    exact hv ((mem_reached c f s v).mpr
      (reached_closed ((mem_reached c f s u).mp hu) he))
  have hc := hcap u v
  omega

lemma sum_internal_zero (f : Flow n) (hf : ∀ u v,f u v= -f v u)
    (S : Finset (Fin n)) : (∑ u∈S,∑ v∈S,f u v)=0 := by
  have hn : (∑ u∈S,∑ v∈S,f u v)= -(∑ u∈S,∑ v∈S,f u v) := by
    calc
      _ = ∑ v∈S,∑ u∈S,f u v := Finset.sum_comm
      _ = ∑ v∈S,∑ u∈S,-f v u := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.sum_congr rfl (fun u _=>hf u v)
      _ = _ := by simp
  omega

lemma value_eq_cut (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (S : Finset (Fin n)) (hs : s∈S) (ht : t∉S) :
    value s f=∑ u∈S,∑ v∈Sᶜ,f u v := by
  have hb : (∑ u∈S,∑ v,f u v)=value s f := by
    apply Finset.sum_eq_single s
    · intro u hu hus
      exact hf.2.2 u hus (fun hut=>ht (hut ▸ hu))
    · exact fun h=>False.elim (h hs)
  have hc : (∑ u∈S,∑ v,f u v)=
      (∑ u∈S,∑ v∈S,f u v)+(∑ u∈S,∑ v∈Sᶜ,f u v) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl S (f u)).symm
  rw [sum_internal_zero f hf.1,zero_add] at hc
  exact hb.symm.trans hc

/-- Failure of the actual finite BFS implies maximum flow. No
max-flow/min-cut result is included in the published input. -/
theorem failure_maximum (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (h : search c f s t=none) : IsMaximum c s t f := by
  refine ⟨hf,?_⟩
  intro g hg
  let S := reached c f s
  have hs : s∈S := source_reached c f s
  have ht : t∉S := target_not_reached c f s t h
  rw [value_eq_cut c s t g hg S hs ht,value_eq_cut c s t f hf S hs ht]
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  have hv' : v∉S := by simpa using hv
  have he : f u v=c u v := cut_saturated c f s hf.2.1 hu hv'
  simpa only [he] using hg.2.1 u v

end ContingencyTables.ResidualSearch

end OAI
