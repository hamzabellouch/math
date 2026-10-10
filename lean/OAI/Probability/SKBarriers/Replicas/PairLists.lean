import Mathlib
import OAI.Probability.SKBarriers.Replicas.PairTimeChain
import OAI.Probability.SKBarriers.Hierarchy.TimeChainAverageAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem pairConstrainedPressure_lists {N : ℕ} (hN : 0<N) (β : ℝ)
    (l r : List (ℝ × ℝ≥0)) (hm : ∀ p∈l++r, p.1∈Icc (0:ℝ) 1)
    (hmono : (l++r).Pairwise (fun p q => p.1 ≤ q.1))
    (ht : chainDuration l+chainDuration r=1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 (chainDuration l)))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 (chainDuration l)) ≤
      2*(scalarTimeChain β (l++r) scalarSpinTerminal 0-
        β^2/4*chainQuadraticPenalty 0 (l++r))-
      (scalarTimeChainAverage β l (scalarTimeChain β r scalarSpinTerminal)
        (fun x => (scalarTimeChainAverage β r scalarSpinTerminal scalarMagnetization x)^2) 0-
        (chainDuration l:ℝ))^2/2 := by
  let L : Fin (l.length+1) → ℝ × ℝ≥0 := Fin.cons (0,0) l.get
  let R : Fin (r.length+1) → ℝ × ℝ≥0 := Fin.snoc r.get (1,0)
  have hL : List.ofFn L=(0,0)::l := by rw [List.ofFn_succ]; simp [L]
  have hR : List.ofFn R=r++[(1,0)] := by rw [List.ofFn_succ']; simp [R,List.concat_eq_append]
  have hLR : List.ofFn (Fin.append L R)=(0,0)::((l++r)++[(1,0)]) := by
    rw [List.ofFn_fin_append,hL,hR]
    simp only [List.cons_append,List.append_assoc]
  have hbounds (p) (hp : p∈(0,0)::((l++r)++[(1,0)])) : p.1∈Icc (0:ℝ) 1 := by
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|hp|rfl
    · norm_num
    · exact hm p (List.mem_append.mpr hp)
    · norm_num
  have hsorted : ((0,0)::((l++r)++[(1,0)])).Pairwise (fun p q => p.1 ≤ q.1) := by
    apply List.pairwise_cons.mpr
    constructor
    · intro p hp
      exact (hbounds p (List.mem_cons_of_mem _ hp)).1
    · apply List.pairwise_append.mpr
      refine ⟨hmono,by simp,?_⟩
      intro p hp q hq
      obtain rfl := List.mem_singleton.mp hq
      exact (hm p hp).2
  have hmass (i) : (Fin.append L R i).1∈Icc (0:ℝ) 1 := by
    apply hbounds
    rw [← hLR]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hmon : Monotone (fun i => (Fin.append L R i).1) := by
    rw [← hLR,List.pairwise_ofFn] at hsorted
    intro i j hij
    rcases lt_or_eq_of_le hij with hij|rfl
    · exact hsorted hij
    · exact le_rfl
  have hdL : (∑ i, ((L i).2:ℝ))=chainDuration l := by
    rw [← NNReal.coe_sum,← chainDuration_ofFn,hL]
    simp
  have hdR : (∑ i, ((R i).2:ℝ))=chainDuration r := by
    rw [← NNReal.coe_sum,← chainDuration_ofFn,hR]
    simp [chainDuration]
  have htime : (∑ i, ((L i).2:ℝ))+(∑ i, ((R i).2:ℝ))=1 := by
    rw [hdL,hdR,← NNReal.coe_add,ht,NNReal.coe_one]
  have H := pairConstrainedPressure_twoChains hN l.length r.length β L R
    (by simp [L]) (by simp [L]) hmass hmon htime (by simpa only [hdL] using hD)
  rw [hL,hR,hdL] at H
  simp only [scalarTimeChainAverage_snoc_zero,scalarTimeChain_snoc_zero,
    scalarTimeChainAverage_cons_zero,List.cons_append] at H
  have hpen : chainQuadraticPenalty 0 ((0,0)::(l++(r++[(1,0)])))=
      chainQuadraticPenalty 0 (l++r) := by
    rw [chainQuadraticPenalty_zero,← List.append_assoc,chainQuadraticPenalty_append,
      chainQuadraticPenalty_singleton]
    simp
  rw [hpen] at H
  have hval : scalarTimeChain β ((0,0)::(l++(r++[(1,0)]))) scalarSpinTerminal=
      scalarTimeChain β (l++r) scalarSpinTerminal := by
    rw [← List.append_assoc,scalarTimeChain]
    simp only [scalarTimeStep_zero]
    exact scalarTimeChain_snoc_zero β 1 (l++r) scalarSpinTerminal
  rw [hval] at H
  exact H

end SK.Analytic

end
end

end OAI
