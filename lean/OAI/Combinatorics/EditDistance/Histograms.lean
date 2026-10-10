import OAI.Combinatorics.EditDistance.HashCuts

namespace OAI

/-!
# Hash separation and finite histogram inequalities
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

section Histogram
variable {J K : Type*} [Fintype J] [Fintype K]

noncomputable def hit (a b : K) : ℝ := if a = b then 1 else 0
omit [Fintype K] in
lemma hit_nonneg (a b : K) : 0 ≤ hit a b := by unfold hit; split <;> norm_num
omit [Fintype K] in
lemma hit_le_one (a b : K) : hit a b ≤ 1 := by unfold hit; split <;> norm_num
omit [Fintype K] in
@[simp] lemma hit_self (a : K) : hit a a = 1 := by simp [hit]

noncomputable def count (f : J → K) (z : K) : ℝ := ∑ j, hit (f j) z
noncomputable def histogramDistance (f g : J → K) : ℝ := ∑ z, |count f z-count g z|

omit [Fintype K] in
lemma count_nonneg (f : J → K) (z : K) : 0 ≤ count f z := sum_nonneg (fun _ _ => hit_nonneg _ _)
lemma histogramDistance_nonneg (f g : J → K) : 0 ≤ histogramDistance f g :=
  sum_nonneg (fun _ _ => abs_nonneg _)

lemma hit_sum (a : K) : ∑ z, hit a z = 1 := by
  classical
  simp [hit]

lemma count_sum (f : J → K) : ∑ z, count f z = Fintype.card J := by
  unfold count
  rw [sum_comm]
  simp only [hit_sum,sum_const,card_univ,nsmul_eq_mul,mul_one]

lemma hit_distance (a b : K) : ∑ z, |hit a z-hit b z| = 2*sep a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [sep]
  · have he (z : K) : |hit a z-hit b z| = hit a z+hit b z := by
      by_cases haz : a = z
      · subst z
        simp [hit,Ne.symm hab]
      · by_cases hbz : b = z
        · subst z
          simp [hit,hab]
        · simp [hit,haz,hbz]
    simp_rw [he]
    rw [sum_add_distrib,hit_sum,hit_sum,sep_eq_one hab]
    norm_num

lemma histogramDistance_le (f g : J → K) : histogramDistance f g ≤ 2*∑ j, sep (f j) (g j) := by
  unfold histogramDistance count
  simp_rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ z : K, ∑ j : J, |hit (f j) z-hit (g j) z| :=
      sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _ = 2*∑ j, sep (f j) (g j) := by
      rw [sum_comm]
      simp_rw [hit_distance]
      rw [mul_sum]

lemma histogramDistance_disjoint (f g : J → K) (h : ∀ i j, f i ≠ g j) :
    histogramDistance f g = 2*(Fintype.card J : ℝ) := by
  have hzero (z : K) : count f z = 0 ∨ count g z = 0 := by
    by_cases hf : ∃ i, f i = z
    · obtain ⟨i,rfl⟩ := hf
      right
      unfold count
      apply sum_eq_zero
      intro j _
      exact ite_eq_right (Ne.symm (h i j))
    · left
      unfold count
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (fun he => hf ⟨i,he⟩)
  have he (z : K) : |count f z-count g z| = count f z+count g z := by
    rcases hzero z with hz|hz
    · rw [hz,zero_sub,abs_neg,abs_of_nonneg (count_nonneg g z),zero_add]
    · rw [hz,sub_zero,abs_of_nonneg (count_nonneg f z),add_zero]
  unfold histogramDistance
  simp_rw [he]
  rw [sum_add_distrib,count_sum,count_sum]
  ring

lemma histogramDistance_lower (f g : J → K) :
    2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, hit (f i) (g j)) ≤
      histogramDistance f g := by
  classical
  by_cases h : ∀ i j, f i ≠ g j
  · rw [histogramDistance_disjoint f g h]
    have hz : (∑ i : J, ∑ j : J, hit (f i) (g j)) = 0 := by
      apply sum_eq_zero
      intro i _
      apply sum_eq_zero
      intro j _
      exact ite_eq_right (h i j)
    rw [hz]
    ring_nf
    rfl
  · push Not at h
    obtain ⟨i,j,hij⟩ := h
    have h1 : 1 ≤ ∑ k : J, hit (f i) (g k) := by
      have hh := single_le_sum (fun k _ => hit_nonneg (f i) (g k)) (mem_univ j)
      simpa only [hij,hit_self] using hh
    have h2 : (∑ k : J, hit (f i) (g k)) ≤ ∑ l : J, ∑ k : J, hit (f l) (g k) :=
      single_le_sum (fun l _ => sum_nonneg (fun k _ => hit_nonneg (f l) (g k))) (mem_univ i)
    have hh : 1-∑ l : J, ∑ k : J, hit (f l) (g k) ≤ 0 := by linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hh).trans
      (histogramDistance_nonneg f g)

end Histogram
end EditCutHash

end OAI
