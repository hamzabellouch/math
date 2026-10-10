import Mathlib
import OAI.Probability.Perceptron.Variational.GridGap

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def heightIndex {d : ℕ} (h : Fin (d+1) → ℝ) (t : ℝ) : Fin (d+2) :=
  ⟨(Finset.univ.filter (fun r => h r < t)).card,by
    have H := Finset.card_le_card (Finset.filter_subset (fun r => h r < t) Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at H
    omega⟩

lemma heightIndex_monotone {d : ℕ} (h : Fin (d+1) → ℝ) : Monotone (heightIndex h) := by
  intro s t hst
  change (Finset.univ.filter (fun r => h r < s)).card ≤ (Finset.univ.filter (fun r => h r < t)).card
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  exact hr.trans_le hst

lemma heightIndex_le_iff {d : ℕ} (h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) (i : Fin (d+1)) : heightIndex h t ≤ i.castSucc ↔ t ≤ h i := by
  constructor
  · intro hi
    by_contra ht
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun r => h r < t) := by
      intro r hr
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact (hh (Finset.mem_Iic.mp hr)).trans_lt (lt_of_not_ge ht)
    have H := Finset.card_le_card hsub
    rw [Fin.card_Iic] at H
    change (Finset.univ.filter (fun r => h r < t)).card ≤ i.val at hi
    omega
  · intro hi
    have hsub : Finset.univ.filter (fun r => h r < t) ⊆ Finset.Iio i := by
      intro r hr
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hr
      apply Finset.mem_Iio.mpr
      by_contra hir
      exact (not_lt_of_ge (hi.trans (hh (le_of_not_gt hir)))) hr
    have H := Finset.card_le_card hsub
    rw [Fin.card_Iio] at H
    exact H

lemma lt_heightIndex_iff {d : ℕ} (h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) (i : Fin (d+1)) : i.castSucc < heightIndex h t ↔ h i < t := by
  simpa only [not_le] using not_congr (heightIndex_le_iff h hh t i)

def heightVariances {K : ℕ} (z : Fin (K+1) → ℝ) (j : Fin K) : ℝ :=
  2*(z j.succ-z j.castSucc)

lemma heightVariances_nonneg {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (j : Fin K) : 0 ≤ heightVariances z j := by
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hz (Fin.castSucc_le_succ j)))

lemma heightVariances_sum {K : ℕ} (z : Fin (K+1) → ℝ) :
    (∑ j, heightVariances z j)=2*(z (Fin.last K)-z 0) := by
  simp only [heightVariances,← Finset.mul_sum,finite_sum_successive_differences]

lemma heightVariances_prefix {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r : ℝ) (hr : r ∈ Set.range z) :
    (∑ j, if z j.succ ≤ r then heightVariances z j else 0)=2*(r-z 0) := by
  obtain ⟨a,rfl⟩ := hr
  have he (j : Fin K) : (if z j.succ ≤ z a then heightVariances z j else 0)=
      2*(min (z a) (z j.succ)-min (z a) (z j.castSucc)) := by
    by_cases hja : j.val < a.val
    · have hs : j.succ ≤ a := by simp only [Fin.le_def,Fin.val_succ]; omega
      have hc : j.castSucc ≤ a := (Fin.castSucc_le_succ j).trans hs
      simp [ite_eq_left (hz hs),min_eq_right (hz hs),min_eq_right (hz hc),heightVariances]
    · have hc : a ≤ j.castSucc := by simp only [Fin.le_def,Fin.val_castSucc]; omega
      have hs : a ≤ j.succ := hc.trans (Fin.castSucc_le_succ j)
      rw [min_eq_left (hz hc),min_eq_left (hz hs),sub_self,mul_zero]
      split_ifs with ht
      · have heq : z j.succ=z j.castSucc := le_antisymm (ht.trans (hz hc)) (hz (Fin.castSucc_le_succ j))
        simp [heightVariances,heq]
      · rfl
  simp only [he,← Finset.mul_sum]
  rw [finite_sum_successive_differences K (fun i => min (z a) (z i))]
  rw [min_eq_left (hz (Fin.le_last a)),min_eq_right (hz (Fin.zero_le a))]

lemma heightIndex_grid_prefix {d K : ℕ} (h : Fin (d+1) → ℝ) (hh : Monotone h)
    (z : Fin (K+1) → ℝ) (hz : Monotone z) (hz0 : z 0=0)
    (hm : ∀ i, h i ∈ Set.range z) (i : Fin (d+1)) :
    varianceLevels (fun j => gridVariance
      (List.ofFn fun r => (heightIndex h (z r.succ),heightVariances z r)) j.castSucc) i=h i := by
  rw [varianceLevels_gridVariance]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,heightIndex_le_iff h hh]
  rw [heightVariances_prefix z hz (h i) (hm i),hz0,sub_zero]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
