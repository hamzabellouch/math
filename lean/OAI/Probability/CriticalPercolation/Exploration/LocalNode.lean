import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Tagged

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree

variable {E I : Type*} (t : I → QueryTree E)

abbrev LocalNode := (i : I) × (t i).Node

def coord (a : LocalNode t) : E := (t a.1).bit a.2

def algorithm (i : I) : MarkedTree E (LocalNode t) :=
  (t i).marked.map (Sigma.mk i)

def raw (order : List I) : MarkedTree E (LocalNode t) :=
  sequence (order.map (algorithm t))

lemma tagged_algorithm (i : I) : (algorithm t i).Tagged (coord t) := by
  apply tagged_map
  exact tagged_marked (t i)

lemma tagged_raw (order : List I) : (raw t order).Tagged (coord t) := by
  apply tagged_sequence
  intro s hs
  rcases List.mem_map.mp hs with ⟨i, _, rfl⟩
  exact tagged_algorithm t i

lemma trace_algorithm (i : I) (ω : E → Bool) :
    (algorithm t i).trace ω =
      ((t i).pathNodes ω).map (fun n => ((t i).bit n, Sigma.mk i n)) := by
  simp [algorithm, trace_map, trace_marked, List.map_map, Function.comp_def]

lemma bits_trace_algorithm (i : I) (ω : E → Bool) :
    ((algorithm t i).trace ω).map Prod.fst = (t i).reads ω := by
  rw [trace_algorithm, List.map_map]
  exact map_bit_pathNodes (t i) ω

lemma index_mem_trace_algorithm (i : I) (ω : E → Bool) (x : E × LocalNode t)
    (h : x ∈ (algorithm t i).trace ω) : x.2.1 = i := by
  rw [trace_algorithm] at h
  rcases List.mem_map.mp h with ⟨n, _, rfl⟩
  rfl

lemma mem_trace_algorithm_self (i : I) (n : (t i).Node) (ω : E → Bool) :
    ((t i).bit n, Sigma.mk i n) ∈ (algorithm t i).trace ω ↔ (t i).visits n ω := by
  rw [trace_algorithm]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨m, hm, hmn⟩
    have he : m = n := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hmn)).2
    subst m
    exact (mem_pathNodes (t i) ω n).mp hm
  · intro h
    exact List.mem_map.mpr ⟨n, (mem_pathNodes (t i) ω n).mpr h, rfl⟩

lemma trace_raw (order : List I) (ω : E → Bool) :
    (raw t order).trace ω = (order.map (fun i => (algorithm t i).trace ω)).flatten := by
  simp [raw, trace_sequence, List.map_map, Function.comp_def]

lemma index_mem_trace_raw (order : List I) (ω : E → Bool) (x : E × LocalNode t)
    (h : x ∈ (raw t order).trace ω) : x.2.1 ∈ order := by
  rw [trace_raw, List.mem_flatten] at h
  rcases h with ⟨xs, hxs, hx⟩
  rcases List.mem_map.mp hxs with ⟨i, hi, rfl⟩
  rwa [index_mem_trace_algorithm t i ω x hx]

lemma mem_bits_trace_raw (order : List I) (ω : E → Bool) (e : E) :
    e ∈ ((raw t order).trace ω).map Prod.fst ↔ ∃ i ∈ order, e ∈ (t i).reads ω := by
  rw [trace_raw]
  simp only [List.map_flatten, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨xs, ⟨ys, ⟨i, hi, rfl⟩, rfl⟩, he⟩
    exact ⟨i, hi, by simpa only [bits_trace_algorithm] using he⟩
  · rintro ⟨i, hi, he⟩
    refine ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, ?_⟩
    simpa only [bits_trace_algorithm] using he

lemma trace_raw_append (pre post : List I) (ω : E → Bool) :
    (raw t (pre++post)).trace ω = (raw t pre).trace ω ++ (raw t post).trace ω := by
  simp [trace_raw]

variable [DecidableEq E] [Fintype E]
def combined (order : List I) : MarkedTree E (LocalNode t) :=
  (raw t order).cached (fun _ => none)

lemma combined_valid (order : List I) : (combined t order).bare.Valid ∅ :=
  cached_empty_valid _

omit [Fintype E] in
lemma combined_tagged (order : List I) : (combined t order).Tagged (coord t) :=
  tagged_cached _ _ (tagged_raw t order) _

lemma trace_combined (order : List I) (ω : E → Bool) :
    (combined t order).trace ω = select ∅ ((raw t order).trace ω) := by
  rw [combined, trace_cached_select]
  · simp [domain]
  · intro e b h; simp at h

lemma fresh_local_node (pre post : List I) (i : I) (n : (t i).Node) (ω : E → Bool)
    (hi : i ∉ pre) (hi' : i ∉ post) (hv : (t i).Valid ∅) :
    ((t i).bit n, Sigma.mk i n) ∈ (combined t (pre++i::post)).trace ω ↔
      (t i).visits n ω ∧ ∀ j ∈ pre, (t i).bit n ∉ (t j).reads ω := by
  rw [trace_combined]
  have he : (raw t (pre++i::post)).trace ω =
      (raw t pre).trace ω ++ (algorithm t i).trace ω ++ (raw t post).trace ω := by
    rw [trace_raw_append]
    simp [raw, MarkedTree.sequence, trace_append, List.append_assoc]
  rw [he, mem_select_block]
  · rw [mem_trace_algorithm_self]
    simp only [Finset.empty_union, List.mem_toFinset, mem_bits_trace_raw, not_exists, not_and]
  · exact fun h => hi (index_mem_trace_raw t pre ω _ h)
  · exact fun h => hi' (index_mem_trace_raw t post ω _ h)
  · rw [bits_trace_algorithm]
    exact reads_nodup (t i) ∅ hv ω

end CriticalPercolation.OrderedQuery

end
end

end OAI
