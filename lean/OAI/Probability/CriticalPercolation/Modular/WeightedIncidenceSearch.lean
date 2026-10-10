import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.IncidenceIdentity
import OAI.Probability.CriticalPercolation.Modular.WeightedQuery

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

def weightedRead (a : E → ℝ) (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e∈st.read, if e∈ω then a e*(1-p) else -a e*p

def quadraticRead (a : E → ℝ) (st : State E) : ℝ := ∑ e∈st.read, (a e)^2

lemma compile_weighted_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (a : E → ℝ) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.weightedSum a p ω + weightedRead a p ω st = weightedRead a p ω out ∧
    t.quadraticCost a ω + quadraticRead a st = quadraticRead a out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hs : weightedRead a p ω (st.open e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.open,Finset.sum_insert he]
      have hs' : weightedRead a p ω (st.closed e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.closed,Finset.sum_insert he]
      have hq : quadraticRead a (st.open e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.open,Finset.sum_insert he]
      have hq' : quadraticRead a (st.closed e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (if ω e then a e*(1-p)+(compile G v n (st.open e)).weightedSum a p ω else
          -a e*p+(compile G v n (st.closed e)).weightedSum a p ω) + weightedRead a p ω st =
          weightedRead a p ω out ∧
        ((a e)^2 + if ω e then (compile G v n (st.open e)).quadraticCost a ω else
          (compile G v n (st.closed e)).quadraticCost a ω) + quadraticRead a st = quadraticRead a out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,ite_true]
        dsimp only at hopen
        rw [hs,hq,ite_eq_left hω] at hopen
        constructor <;> linarith [hopen.1,hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,ite_false]
        dsimp only at hclosed
        rw [hs',hq',ite_eq_right hω] at hclosed
        constructor <;> linarith [hclosed.1,hclosed.2]
    · simp [SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]

variable [Fintype E]

lemma tree_weighted (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) (p : ℝ) :
    (tree G v).weightedSum a p ω = ∑ e, if e∈G.incidentEdges (G.cluster ω v) then
      (if e∈ω then a e*(1-p) else -a e*p) else 0 := by
  have h := (compile_weighted_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω a p).1
  change (tree G v).weightedSum a p ω + weightedRead a p ω ⟨∅,∅⟩ =
    weightedRead a p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [weightedRead,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then a e*(1-p) else -a e*p) else 0 := by
      simp only [←Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

lemma tree_quadratic (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) :
    (tree G v).quadraticCost a ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (a e)^2 else 0 := by
  have h := (compile_weighted_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω a 0).2
  change (tree G v).quadraticCost a ω + quadraticRead a ⟨∅,∅⟩ =
    quadraticRead a ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [quadraticRead,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then (a e)^2 else 0 := by
      simp only [←Finset.sum_filter]
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

end OAI
