import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.QueryTree
import OAI.Probability.CriticalPercolation.Exploration.State

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

noncomputable def initial (S : Finset V) : State V E := ⟨S,∅⟩
noncomputable def search (G : BondGraph V E) (S : Finset V) : SearchTree E (State V E) :=
  compile G (Fintype.card E) (initial S)

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
lemma initial_consistent (G : BondGraph V E) (S : Finset V) (ω : E → Bool) :
    Consistent G (initial S) ω := by
  intro e he
  exact (Finset.notMem_empty e he).elim

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
lemma initial_sound (G : BondGraph V E) (S : Finset V) (ω : E → Bool) :
    Sound G (S : Set V) (initial S) ω := by
  intro v hv
  exact ⟨v,hv,.refl _⟩

lemma search_valid (G : BondGraph V E) (S : Finset V) : (search G S).Valid ∅ :=
  compile_valid G _ _

lemma search_reached (G : BondGraph V E) (S : Finset V) (ω : E → Bool) (v : V) :
    v ∈ ((search G S).run ω).reached ↔
      ∃ a ∈ S, (G.openGraph {e | ω e = true}).Reachable a v := by
  obtain ⟨hc,hs,hm⟩ := compile_invariants G (S : Set V) (Fintype.card E) (initial S) ω
    (initial_consistent G S ω) (initial_sound G S ω)
  constructor
  · exact hs v
  · rintro ⟨a,ha,hav⟩
    have he := compile_exhausted G (Fintype.card E) (initial S) ω (by simp [initial])
    have hcl : ∀ u ∈ ((search G S).run ω).reached, ∀ t,
        (G.openGraph {e | ω e = true}).Adj u t → t ∈ ((search G S).run ω).reached := by
      intro u hu t hut
      obtain ⟨⟨e,hew,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hut
      have hread : e ∈ ((search G S).run ω).read := by
        by_contra hn
        exact he ⟨e,hn,u,hu,by simp [heq]⟩
      exact hc e hread hew t (by simp [heq])
    have hh := ((G.openGraph {e | ω e = true}).reachable_iff_reflTransGen a v).mp hav
    clear hav
    induction hh with
    | refl => exact hm ha
    | tail _ huv ih => exact hcl _ ih _ huv

lemma search_reads (G : BondGraph V E) (S : Finset V) (ω : E → Bool) (e : E) :
    e ∈ (search G S).reads ω ↔
      ∃ v ∈ G.ends e, ∃ a ∈ S, (G.openGraph {e | ω e = true}).Reachable a v := by
  have he := compile_exhausted G (Fintype.card E) (initial S) ω (by simp [initial])
  have hrd : ((search G S).run ω).read = ((search G S).reads ω).toFinset := by
    simpa only [search,initial,Finset.empty_union] using compile_read G (Fintype.card E) (initial S) ω
  constructor
  · intro hed
    have hs : Sound G Set.univ (initial S) ω := by
      intro v _
      exact ⟨v,Set.mem_univ _,.refl _⟩
    obtain ⟨v,hv,hev⟩ := compile_reads_incident G (Fintype.card E) (initial S) ω
      (initial_consistent G S ω) hs e hed
    exact ⟨v,hev,(search_reached G S ω v).mp hv⟩
  · rintro ⟨v,hve,a,ha,hav⟩
    have hv := (search_reached G S ω v).mpr ⟨a,ha,hav⟩
    have hr : e ∈ ((search G S).run ω).read := by
      by_contra hn
      exact he ⟨e,hn,v,hv,hve⟩
    rw [hrd] at hr
    exact List.mem_toFinset.mp hr

noncomputable def pair (G : BondGraph V E) (a b : V) : SearchTree E (State V E) :=
  search G {a,b}

lemma pair_reads (G : BondGraph V E) (a b : V) (ω : E → Bool) (e : E) :
    e ∈ (pair G a b).reads ω ↔
      ∃ v ∈ G.ends e, (G.openGraph {e | ω e = true}).Reachable a v ∨
        (G.openGraph {e | ω e = true}).Reachable b v := by
  simp only [pair,search_reads,Finset.mem_insert,Finset.mem_singleton,exists_eq_or_imp, exists_eq_left]

end CriticalPercolation.ExactExposure

namespace CriticalPercolation
namespace SearchTree
variable {E R : Type*}
def bare : SearchTree E R → QueryTree E
  | .done _ => .stop
  | .ask e l r => .ask e l.bare r.bare

lemma bare_reads (T : SearchTree E R) (ω : E → Bool) : T.bare.reads ω = T.reads ω := by
  induction T with
  | done _ => rfl
  | ask e l r hl hr => simp only [bare,QueryTree.reads,reads,hl,hr]

lemma bare_valid [DecidableEq E] (T : SearchTree E R) (used : Finset E) (h : T.Valid used) :
    T.bare.Valid used := by
  induction T generalizing used with
  | done _ => trivial
  | ask e l r hl hr => exact ⟨h.1,hl _ h.2.1,hr _ h.2.2⟩

lemma bare_run_eq (T : SearchTree E R) (ω η : E → Bool) (h : T.bare.run ω = T.bare.run η) :
    T.run ω = T.run η ∧ ∀ e ∈ T.reads ω, ω e = η e := by
  induction T with
  | done _ => exact ⟨rfl,by simp [reads]⟩
  | ask e l r hl hr =>
    simp only [bare,QueryTree.run] at h
    cases he : ω e <;> cases he' : η e
    · simp only [he,he',Bool.false_eq_true,↓reduceIte,Sum.inl.injEq] at h
      obtain ⟨hout,hbits⟩ := hl h
      simp only [run,reads,he,he',Bool.false_eq_true,↓reduceIte]
      refine ⟨hout,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he.trans he'.symm
      · exact hbits f hf
    · simp [he,he'] at h
    · simp [he,he'] at h
    · simp only [he,he',↓reduceIte,Sum.inr.injEq] at h
      obtain ⟨hout,hbits⟩ := hr h
      simp only [run,reads,he,he',↓reduceIte]
      refine ⟨hout,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he.trans he'.symm
      · exact hbits f hf
end SearchTree
end CriticalPercolation

end
end

end OAI
