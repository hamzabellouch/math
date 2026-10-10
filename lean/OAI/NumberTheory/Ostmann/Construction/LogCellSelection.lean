import OAI.NumberTheory.Ostmann.Construction.GiantRobustMean
import OAI.NumberTheory.Ostmann.Construction.LogCellFinitePartition

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

theorem exists_positive_logCell (P : Finset ℕ) (G h a : ℝ) (F : ℕ → ℝ)
    (hh : 5≤h) (ha : 0<a) (hP : ∀p∈P,G≤Real.log p ∧ Real.log p≤G+h)
    (hmean : a*h≤∑p∈P,F p) :
    ∃c∈logBlockCenters G h,a/4<∑p∈P,Ostmann.smoothPartition (Real.log p-c)*F p := by
  by_contra hn
  push Not at hn
  have hsum := Finset.sum_le_sum (s := logBlockCenters G h) hn
  rw [logBlockCenters_weighted_partition P G h F hP] at hsum
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hc := logBlockCenters_card_le G h (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hc (by positivity : 0≤a/4)
  nlinarith

lemma smooth_cell_robust_point_le (c : ℝ) (hc : 3≤c) (p : ℕ) (u m : ℝ)
    (hu : 0≤u) :
    Ostmann.smoothPartition (Real.log p-c)*(Real.log p/(p:ℝ))*(u-2*|m-u|)≤
      (c+1)*(Ostmann.smoothPartition (Real.log p-c)/(p:ℝ)*m) := by
  by_cases hz : Ostmann.smoothPartition (Real.log p-c)=0
  · simp only [hz,zero_mul,zero_div,mul_zero,le_refl]
  have hs := Ostmann.smoothPartition_support_subset hz
  have he : 0≤|m-u| := abs_nonneg _
  have hm : u-|m-u|≤ m := by
    have h := le_abs_self (u-m)
    rw [abs_sub_comm] at h
    linarith
  have ht₁ : 0≤c+1-Real.log p := by linarith [hs.2]
  have ht₂ : 0≤2*Real.log p-c-1 := by linarith [hs.1]
  have hnon := add_nonneg (mul_nonneg ht₁ hu) (mul_nonneg ht₂ he)
  have hmul := mul_le_mul_of_nonneg_left hm (show 0≤c+1 by linarith)
  have hbase : Real.log p*(u-2*|m-u|)≤(c+1)*m := by nlinarith
  have hw : 0≤Ostmann.smoothPartition (Real.log p-c)/(p:ℝ) :=
    div_nonneg (Ostmann.smoothPartition_nonneg _) (Nat.cast_nonneg p)
  have h := mul_le_mul_of_nonneg_left hbase hw
  convert h using 1 <;> ring

theorem smooth_cell_giant_robust_le (d : Decomposition) (X : ℕ) (P : Finset ℕ)
    (c : ℝ) (hc : 3≤c) (hP : ∀p∈P,0≤giantSupportMean d p) :
    (∑p∈P,Ostmann.smoothPartition (Real.log p-c)*(Real.log p/(p:ℝ))*giantRobustMean d X p)≤
      (c+1)*(∑p∈P,logCellWeight c p*giantEmpiricalMean d X p) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p hp =>
    smooth_cell_robust_point_le c hc p (giantSupportMean d p) (giantEmpiricalMean d X p) (hP p hp))

end Ostmann.Construction

end

end OAI
