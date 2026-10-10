import OAI.NumberTheory.TotientAsymptotic.ThirdPrimeSize
import OAI.NumberTheory.TotientAsymptotic.ComparisonErrorBudget

namespace OAI

/-! Split an ordered coordinate vector at its last coordinate above a threshold. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

 def coordinateActivePrefix (n k : ℕ) (u : ℝ) : ℕ :=
  Nat.findGreatest (fun j => u < fordPrimeCoordinate n j) k

lemma coordinate_active_prefix_bounds (n k : ℕ) (u : ℝ) :
    coordinateActivePrefix n k u ≤ k ∧
    (∀ j,1 ≤ j → j ≤ coordinateActivePrefix n k u → u < fordPrimeCoordinate n j) ∧
    (∀ j,coordinateActivePrefix n k u < j → j ≤ k → fordPrimeCoordinate n j ≤ u) := by
  classical
  let r := coordinateActivePrefix n k u
  have hr : r ≤ k := Nat.findGreatest_le k
  refine ⟨hr,?_,?_⟩
  · intro j hj hjr
    have hr0 : r ≠ 0 := by omega
    have hpr : u < fordPrimeCoordinate n r := (Nat.findGreatest_eq_iff.mp rfl).2.1 hr0
    exact hpr.trans_le (ford_coordinate_antitone n hjr)
  · intro j hrj hjk
    have hh := Nat.findGreatest_is_greatest hrj hjk
    exact le_of_not_gt hh

lemma sum_a_range_eq_Icc (k : ℕ) :
    (∑ j ∈ Finset.range k,a (j+1)) = ∑ j ∈ Finset.Icc 1 k,a j := by
  refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hj; omega⟩
  · intro i hi j hj he
    omega
  · intro j hj
    have hh := Finset.mem_Icc.mp hj
    exact ⟨j-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro j hj
    rfl

lemma sum_a_fin_le_square (k : ℕ) : (∑ j : Fin k,a (j.val+1)) ≤ (k:ℝ)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (j+1)),sum_a_range_eq_Icc]
  exact sum_a_le_square k

lemma coordinate_score_tail_le (n k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (∑ j ∈ Finset.range k,a (j+1)*fordPrimeCoordinate n (j+1)) ≤
      (∑ j ∈ Finset.range (coordinateActivePrefix n k u),a (j+1)*fordPrimeCoordinate n (j+1))+
      u*(k:ℝ)^2 := by
  let r := coordinateActivePrefix n k u
  obtain ⟨hr,hlo,hhi⟩ := coordinate_active_prefix_bounds n k u
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => a (j+1)*fordPrimeCoordinate n (j+1)) hr
  have htail : (∑ j ∈ Finset.Ico r k,a (j+1)*fordPrimeCoordinate n (j+1)) ≤
      u*(∑ j ∈ Finset.Icc 1 k,a j) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico r k,u*a (j+1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hm := Finset.mem_Ico.mp hj
        have ha := a_pos (show 1 ≤ j+1 by omega)
        have hc := hhi (j+1) (by omega) (by omega)
        nlinarith only [mul_le_mul_of_nonneg_left hc ha.le]
      _ = u*(∑ j ∈ Finset.Ico r k,a (j+1)) := by rw [Finset.mul_sum]
      _ ≤ u*(∑ j ∈ Finset.range k,a (j+1)) := by
        apply mul_le_mul_of_nonneg_left _ hu
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
        · intro j hj _
          exact (a_pos (by omega)).le
      _ = _ := by rw [sum_a_range_eq_Icc]
  have ha := mul_le_mul_of_nonneg_left (sum_a_le_square k) hu
  dsimp [r] at hsplit htail
  linarith

lemma coordinate_active_prefix_score {n k : ℕ} {L : ℕ} {T : ℝ}
    (hL : 3 ≤ L) (hT : ((L:ℝ)+1)*(k:ℝ)^2 < T)
    (hscore : T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) :
    ∃ r : ℕ,0 < r ∧ r ≤ k ∧
      (∀ j : Fin r,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) ∧
      T-((L:ℝ)+1)*(k:ℝ)^2 ≤ ∑ j : Fin r,a (j.val+1)*fordPrimeCoordinate n (j.val+1) := by
  let r := coordinateActivePrefix n k ((L:ℝ)+1)
  obtain ⟨hr,hlo,_⟩ := coordinate_active_prefix_bounds n k ((L:ℝ)+1)
  have hu : 0 ≤ (L:ℝ)+1 := by positivity
  have ht := coordinate_score_tail_le n k hu
  have hs : T ≤ ∑ j ∈ Finset.range k,a (j+1)*fordPrimeCoordinate n (j+1) := by
    simpa only [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (j+1)*fordPrimeCoordinate n (j+1))] using hscore
  have hr0 : 0 < r := by
    by_contra hh
    have he : r=0 := by omega
    change (∑ j ∈ Finset.range k,a (j+1)*fordPrimeCoordinate n (j+1)) ≤
      (∑ j ∈ Finset.range r,a (j+1)*fordPrimeCoordinate n (j+1))+((L:ℝ)+1)*(k:ℝ)^2 at ht
    rw [he,Finset.sum_range_zero,zero_add] at ht
    linarith
  refine ⟨r,hr0,hr,?_,?_⟩
  · intro j
    have hh := hlo (j.val+1) (by omega) (by have := j.isLt; omega)
    have hcoord : 0 < fordPrimeCoordinate n (j.val+1) := by
      have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
      linarith
    rw [fordPrimeCoordinate_eq_raw_of_pos hcoord] at hh
    exact hh.le
  · rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (j+1)*fordPrimeCoordinate n (j+1))]
    linarith

end TotientAsymptotic

end

end OAI
