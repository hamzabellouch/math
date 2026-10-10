import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarAtomic
import OAI.Probability.SKBarriers.Scalar.PartitionChain

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileCDF_bounds (k : ℕ) (Q : Fin (k+1) → ℝ) (s : ℝ) :
    quantileCDF k Q s ∈ Icc (0:ℝ) 1 := by
  rw [quantileCDF_formula]
  constructor
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  · rw [← uniformAtom_sum k]
    exact Finset.sum_le_sum (fun _ _ => by split_ifs <;> first | exact le_rfl | positivity)

theorem quantileCDF_monotone (k : ℕ) (Q : Fin (k+1) → ℝ) : Monotone (quantileCDF k Q) := by
  intro s t hst
  simp only [quantileCDF_formula]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : Q j ≤ s
  · simp only [ite_eq_left hj,ite_eq_left (hj.trans hst),le_refl]
  · simp only [ite_eq_right hj]
    split_ifs <;> positivity

theorem monotone_cons_zero_quantiles {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) : Monotone (Fin.cons (α := fun _ => ℝ) 0 Q) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact hQ (Fin.castSucc_le_succ j)

theorem quantile_knots_gap (k : ℕ) (Q : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    Fin.cons (α := fun _ => ℝ) 0 Q i.succ-Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc=cumulativeGapMap k Q i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rfl

theorem quantileCDF_on_interval {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : Monotone Q)
    (i : Fin (k+1)) (z : ℝ) (hz : z ∈ Ico (Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc) (Q i)) :
    quantileCDF k Q z=quantileMass k i := by
  have he (j : Fin (k+1)) : Q j ≤ z ↔ j < i := by
    constructor
    · intro hj
      by_contra hji
      have H := hQ (le_of_not_gt hji)
      linarith [hz.2]
    · intro hji
      cases i using Fin.cases with
      | zero => simp at hji
      | succ l =>
        have hj : j ≤ l.castSucc := by simpa only [Fin.le_def,Fin.lt_def,Fin.val_castSucc] using (Nat.le_of_lt_succ hji)
        exact (hQ hj).trans hz.1
  rw [quantileCDF_formula]
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter (fun j : Fin (k+1) => j < i))=Finset.Iio i := by ext j; simp
  rw [hs,Finset.sum_const,Fin.card_Iio]
  simp only [nsmul_eq_mul,quantileMass,div_eq_mul_inv]

theorem quantile_prefix_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) :
    ∃ l : List (ℝ × ℝ≥0),
      (chainDuration l:ℝ)=Q (Fin.last k) ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β f, scalarTimeChain β l f=scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) f := by
  let q := Fin.cons (α := fun _ => ℝ) 0 Q
  let hq := monotone_cons_zero_quantiles Q hQ h0
  let l := partitionTimeChain (k+1) q hq (quantileMass k)
  refine ⟨l,?_,?_,?_,?_⟩
  · have H := partitionTimeChain_duration (k+1) q hq (quantileMass k)
    simpa only [q,← Fin.succ_last,Fin.cons_succ,Fin.cons_zero,sub_zero] using H
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    change quantileMass k i ∈ Icc (0:ℝ) 1
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
      exact_mod_cast i.isLt.le
  · change TimeChainModels (quantileCDF k Q) (q 0) (partitionTimeChain (k+1) q hq (quantileMass k))
    apply partitionTimeChain_models
    intro i z hz
    exact quantileCDF_on_interval Q hQ i z hz
  · intro β f
    dsimp only [l,partitionTimeChain]
    rw [scalarTimeChain_ofFn]
    congr 2
    funext i
    simp only [NNReal.coe_mk, q]
    rw [quantile_knots_gap]
end SK.Analytic

end
end

end OAI
