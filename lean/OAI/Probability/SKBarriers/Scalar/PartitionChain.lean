import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.TimeChainSplit

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

@[simp] theorem chainDuration_append (l r : List (ℝ × ℝ≥0)) :
    chainDuration (l++r)=chainDuration l+chainDuration r := by
  simp [chainDuration]

theorem TimeChainModels.append {α : ℝ → ℝ} {s : ℝ} {l r : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) (hr : TimeChainModels α (s+chainDuration l) r) :
    TimeChainModels α s (l++r) := by
  induction l generalizing s with
  | nil => simpa only [chainDuration_nil,NNReal.coe_zero,add_zero,List.nil_append] using hr
  | cons p l ih =>
    rcases p with ⟨m,t⟩
    rcases hl with ⟨hc,hl⟩
    exact ⟨hc,ih hl (by simpa only [chainDuration_cons,NNReal.coe_add,add_assoc] using hr)⟩

def partitionTimeChain (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (m : Fin n → ℝ) : List (ℝ × ℝ≥0) :=
  List.ofFn (fun i : Fin n => (m i,NNReal.mk (q i.succ-q i.castSucc) (sub_nonneg.mpr (hq (Fin.castSucc_le_succ i)))))

theorem partitionTimeChain_cons (n : ℕ) (q : Fin (n+2) → ℝ) (hq : Monotone q)
    (m : Fin (n+1) → ℝ) :
    partitionTimeChain (n+1) q hq m =
      (m 0,NNReal.mk (q 1-q 0) (sub_nonneg.mpr (hq (Fin.zero_le _))))::
        partitionTimeChain n (fun i => q i.succ)
          (fun _ _ h => hq (Fin.succ_le_succ_iff.mpr h)) (fun i => m i.succ) := by
  simp only [partitionTimeChain,List.ofFn_succ]
  rfl

theorem partitionTimeChain_duration (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (m : Fin n → ℝ) : (chainDuration (partitionTimeChain n q hq m):ℝ)=q (Fin.last n)-q 0 := by
  simp only [partitionTimeChain,chainDuration,List.map_ofFn,List.sum_ofFn,
    NNReal.coe_sum,NNReal.coe_mk,Function.comp_apply,Finset.sum_sub_distrib]
  have H₁ := Fin.sum_univ_succ q
  have H₂ := Fin.sum_univ_castSucc q
  linarith

theorem partitionTimeChain_models (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (m : Fin n → ℝ) {α : ℝ → ℝ}
    (hc : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i) :
    TimeChainModels α (q 0) (partitionTimeChain n q hq m) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [partitionTimeChain,List.ofFn_succ,TimeChainModels,NNReal.coe_mk]
    constructor
    · intro z hz
      apply hc 0 z
      simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one,add_sub_cancel] using hz
    · have H := ih (fun i => q i.succ) (fun _ _ h => hq (Fin.succ_le_succ_iff.mpr h))
        (fun i => m i.succ) (fun i z hz => hc i.succ z hz)
      simpa only [partitionTimeChain,Fin.succ_zero_eq_one,Fin.castSucc_zero,Fin.succ_castSucc,add_sub_cancel] using H

end SK.Analytic

end
end

end OAI
