import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.QueryMartingale
import OAI.Probability.CriticalPercolation.Exploration.IncidenceSearch

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

 def readSum (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e ∈ st.read, if e∈ω then 1-p else -p

lemma compile_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.queryCount ω + st.read.card = out.read.card ∧
      t.centeredSum p ω + readSum p ω st = readSum p ω out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.queryCount,SearchTree.centeredSum]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hcard : (insert e st.read).card = st.read.card + 1 := Finset.card_insert_of_notMem he
      have hsum : readSum p ω (st.open e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.open,Finset.sum_insert he]
      have hsum' : readSum p ω (st.closed e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (1 + if ω e then (compile G v n (st.open e)).queryCount ω else
          (compile G v n (st.closed e)).queryCount ω) + st.read.card = out.read.card ∧
        (if ω e then (1-p)+(compile G v n (st.open e)).centeredSum p ω else
          -p+(compile G v n (st.closed e)).centeredSum p ω) + readSum p ω st = readSum p ω out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,ite_true]
        dsimp only at hopen
        constructor
        · have hh := hopen.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum,ite_eq_left hω] at hopen
          linarith [hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,ite_false]
        dsimp only at hclosed
        constructor
        · have hh := hclosed.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum',ite_eq_right hω] at hclosed
          linarith [hclosed.2]
    · simp [SearchTree.run,SearchTree.queryCount,SearchTree.centeredSum]

variable [Fintype E]
 def tree (G : BondGraph V E) (v : V) : SearchTree E (State E) :=
  compile G v (Fintype.card E + 1) ⟨∅,∅⟩

lemma tree_valid (G : BondGraph V E) (v : V) : (tree G v).Valid ∅ :=
  compile_valid G v _ _

lemma tree_read (G : BondGraph V E) (v : V) (ω : Set E) :
    (((tree G v).run (fun e => decide (e∈ω))).read : Set E) =
      G.incidentEdges (G.cluster ω v) := by
  have hg : Good G v ω (⟨∅,∅⟩ : State E) := by simp [Good]
  have hh := compile_terminal G v ω (Fintype.card E+1) ⟨∅,∅⟩ hg (by simp)
  exact (terminal_cluster G v ω _ hh.1 hh.2).2

lemma tree_mem_read (G : BondGraph V E) (v : V) (ω : Set E) (e : E) :
    e ∈ ((tree G v).run (fun a => decide (a∈ω))).read ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  exact Set.ext_iff.mp (tree_read G v ω) e

lemma tree_count (G : BondGraph V E) (v : V) (ω : Set E) :
    (tree G v).queryCount ω = (G.incidentEdges (G.cluster ω v)).toFinset.card := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω (0:ℝ)).1
  change (tree G v).queryCount ω + (∅ : Finset E).card =
    ((tree G v).run (fun e => decide (e∈ω))).read.card at h
  simp only [Finset.card_empty,add_zero] at h
  refine h.trans (congrArg Finset.card ?_)
  ext e
  rw [Set.mem_toFinset]
  exact tree_mem_read G v ω e

lemma tree_centered (G : BondGraph V E) (v : V) (ω : Set E) (p : ℝ) :
    (tree G v).centeredSum p ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0 := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω p).2
  change (tree G v).centeredSum p ω + readSum p ω ⟨∅,∅⟩ =
    readSum p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [readSum,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then 1-p else -p) else 0 := by
      simp only [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
