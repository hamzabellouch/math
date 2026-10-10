import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFSuffixSemigroup

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def positiveTimeChain (l : List (ℝ × ℝ≥0)) : List (ℝ × ℝ≥0) := l.filter (fun p => p.2≠0)

@[simp] theorem chainDuration_positiveTimeChain (l : List (ℝ × ℝ≥0)) :
    chainDuration (positiveTimeChain l)=chainDuration l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    by_cases hd : d=0
    · simpa [positiveTimeChain,hd,chainDuration_cons] using ih
    · simp only [SK.Analytic.positiveTimeChain,List.filter_cons,hd,ne_eq,not_false_eq_true,decide_true,ite_true,chainDuration_cons] at *
      rw [ih]

theorem positiveTimeChain_mem {l : List (ℝ × ℝ≥0)} {p : ℝ × ℝ≥0} (hp : p∈positiveTimeChain l) :
    p∈l ∧ 0<p.2 := by
  simpa only [positiveTimeChain,List.mem_filter,decide_eq_true_eq,ne_eq,pos_iff_ne_zero] using hp

theorem TimeChainModels.positiveTimeChain {α : ℝ → ℝ} {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : TimeChainModels α s (positiveTimeChain l) := by
  induction l generalizing s with
  | nil => trivial
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    by_cases hd : d=0
    · simpa [SK.Analytic.positiveTimeChain,hd] using ih ht
    · simp only [SK.Analytic.positiveTimeChain,List.filter_cons,hd,ne_eq,not_false_eq_true,decide_true,ite_true]
      exact ⟨hc,ih ht⟩

theorem TimeChainModels.sorted {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) (hpos : ∀ p∈l,0<p.2) : l.Pairwise (fun p q => p.1≤q.1) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hd : 0<(d:ℝ) := hpos (m,d) (List.mem_cons_self ..)
    have he : α s=m := hc s ⟨le_rfl,by linarith⟩
    apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      rw [← he]
      exact (hα (le_add_of_nonneg_right d.coe_nonneg)).trans
        (ht.mass_bounds hα hq (hpos q (List.mem_cons_of_mem _ hq))).1
    · exact ih ht (fun q hq => hpos q (List.mem_cons_of_mem _ hq))

theorem quantile_interval_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), (chainDuration l:ℝ)=t-s ∧
      (∀ p∈l,p.1∈Icc (0:ℝ) 1) ∧ (∀ p∈l,0<p.2) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hst.trans ht⟩
  have hsplit : chainDuration l=Real.toNNReal (t-s)+Real.toNNReal (1-t) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith)]
    ring
  obtain ⟨l₁,_,hd₁,_,hm₁,_,hmodel₁,_,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm s hmodel _ _ hsplit
  refine ⟨positiveTimeChain l₁,?_,fun p hp => hm₁ p (positiveTimeChain_mem hp).1,
    fun p hp => (positiveTimeChain_mem hp).2,hmodel₁.positiveTimeChain⟩
  rw [chainDuration_positiveTimeChain,hd₁,Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

end SK.Analytic

end
end

end OAI
