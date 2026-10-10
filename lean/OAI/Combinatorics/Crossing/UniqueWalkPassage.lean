import Mathlib.Combinatorics.SimpleGraph.Paths

namespace OAI

namespace Zarankiewicz

def UniqueWalkVisit {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (x : V) : Prop :=
  ∀ i j : ℕ, i ≤ p.length → j ≤ p.length → p.getVert i=x → p.getVert j=x → i=j

theorem walk_dart_parameters {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    ∃ i : ℕ, i < p.length ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hd
  have he := SimpleGraph.Walk.darts_getElem_eq_getVert (p:=p) i.val i.isLt
  have hd' := hi.symm.trans he
  refine ⟨i.val,by simpa only [p.length_darts] using i.isLt,?_,?_⟩
  · exact congrArg (fun r : G.Dart => r.fst) hd'
  · exact congrArg (fun r : G.Dart => r.snd) hd'

theorem unique_walk_visit_passage {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (x : V) (hunique : UniqueWalkVisit p x)
    (d e : G.Dart) (hd : d ∈ p.darts) (he : e ∈ p.darts) (hdx : d.snd=x) (hex : e.fst=x) :
    ∃ i : ℕ, i+1 < p.length ∧ d.fst=p.getVert i ∧
      x=p.getVert (i+1) ∧ e.snd=p.getVert (i+2) := by
  obtain ⟨i,hi,hdi,hdi'⟩ := walk_dart_parameters p d hd
  obtain ⟨j,hj,hej,hej'⟩ := walk_dart_parameters p e he
  have hij : i+1=j := hunique (i+1) j (by omega) (by omega) (hdi'.symm.trans hdx) (hej.symm.trans hex)
  refine ⟨i,by omega,hdi,hdx.symm.trans hdi',?_⟩
  simpa only [← hij,Nat.add_assoc] using hej'

theorem bypass_unique_walk_visit_passage {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (x : V) (hunique : UniqueWalkVisit p x)
    (d e : G.Dart) (hd : d ∈ p.bypass.darts) (he : e ∈ p.bypass.darts) (hdx : d.snd=x) (hex : e.fst=x) :
    ∃ i : ℕ, i+1 < p.length ∧ d.fst=p.getVert i ∧
      x=p.getVert (i+1) ∧ e.snd=p.getVert (i+2) :=
  unique_walk_visit_passage p x hunique d e (p.darts_bypass_subset_darts hd)
    (p.darts_bypass_subset_darts he) hdx hex

end Zarankiewicz

end OAI
