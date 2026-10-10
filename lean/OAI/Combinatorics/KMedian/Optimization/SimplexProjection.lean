import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Simplex
open Finset
variable {ι : Type} [Fintype ι] [Nonempty ι]

def upper (x : ι → ℚ) (a : ι) : Finset ι := univ.filter (fun i => x a ≤ x i)

omit [Nonempty ι] in
theorem mem_upper_self (x : ι → ℚ) (a : ι) : a ∈ upper x a := by simp [upper]

omit [Nonempty ι] in
theorem upper_card_pos (x : ι → ℚ) (a : ι) : 0 < (upper x a).card :=
  card_pos.mpr ⟨a,mem_upper_self x a⟩

def threshold (x : ι → ℚ) (k : ℚ) (a : ι) : ℚ :=
  ((∑ i ∈ upper x a, x i)-k)/(upper x a).card

def level (x : ι → ℚ) (k : ℚ) : ℚ :=
  (univ.image (threshold x k)).max' (univ_nonempty.image _)

def project (x : ι → ℚ) (k : ℚ) (i : ι) : ℚ := max 0 (x i-level x k)

theorem threshold_le_level (x : ι → ℚ) (k : ℚ) (a : ι) :
    threshold x k a ≤ level x k :=
  le_max' _ _ (mem_image.mpr ⟨a,mem_univ _,rfl⟩)

theorem level_attained (x : ι → ℚ) (k : ℚ) : ∃ a, level x k=threshold x k a := by
  obtain ⟨a,_,ha⟩ := mem_image.mp (max'_mem (univ.image (threshold x k))
    (univ_nonempty.image _))
  exact ⟨a,ha.symm⟩

omit [Nonempty ι] in
theorem threshold_sum (x : ι → ℚ) (k : ℚ) (a : ι) :
    ∑ i ∈ upper x a, (x i-threshold x k a)=k := by
  have hc : ((upper x a).card:ℚ) ≠ 0 := by exact_mod_cast (upper_card_pos x a).ne'
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,threshold]
  field_simp
  ring

theorem project_nonneg (x : ι → ℚ) (k : ℚ) (i : ι) : 0 ≤ project x k i := le_max_left _ _

theorem project_sum (x : ι → ℚ) (k : ℚ) (hk : 0 < k) : ∑ i, project x k i=k := by
  obtain ⟨b,hb⟩ := level_attained x k
  have hlow : k ≤ ∑ i, project x k i := by
    calc
      k = ∑ i ∈ upper x b, (x i-level x k) := by rw [hb,threshold_sum]
      _ ≤ ∑ i ∈ upper x b, project x k i := sum_le_sum (fun _ _ => le_max_right _ _)
      _ ≤ ∑ i, project x k i := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun i _ _ => project_nonneg x k i)
  let A := univ.filter (fun i => 0 < project x k i)
  have hA : A.Nonempty := by
    by_contra h
    have hz : ∀ i, project x k i=0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun hp => h ⟨i,mem_filter.mpr ⟨mem_univ _,hp⟩⟩))
        (project_nonneg x k i)
    simp only [hz,sum_const_zero] at hlow
    exact (not_le_of_gt hk) hlow
  obtain ⟨a,ha,hmin⟩ := A.exists_min_image x hA
  have ha' : 0 < project x k a := (mem_filter.mp ha).2
  have hax : level x k < x a := by
    simpa only [project,lt_max_iff,lt_self_iff_false,false_or,sub_pos] using ha'
  have hset : A=upper x a := by
    ext i
    constructor
    · intro hi
      exact mem_filter.mpr ⟨mem_univ _,hmin i hi⟩
    · intro hi
      have hxi := (mem_filter.mp hi).2
      apply mem_filter.mpr
      exact ⟨mem_univ _,lt_max_of_lt_right (sub_pos.mpr (hax.trans_le hxi))⟩
  have hout : ∑ i, project x k i=∑ i ∈ upper x a, (x i-level x k) := by
    rw [← hset]
    calc
      _ = ∑ i ∈ A, project x k i := (sum_subset (subset_univ _) (by
        intro i _ hi
        exact le_antisymm (le_of_not_gt (fun hp => hi (mem_filter.mpr ⟨mem_univ _,hp⟩)))
          (project_nonneg x k i))).symm
      _ = _ := sum_congr rfl (fun i hi => by
        have hp : level x k < x i := by
          simpa only [project,lt_max_iff,lt_self_iff_false,false_or,sub_pos]
            using (mem_filter.mp hi).2
        exact max_eq_right (sub_nonneg.mpr hp.le))
  apply le_antisymm _ hlow
  rw [hout]
  calc
    _ ≤ ∑ i ∈ upper x a, (x i-threshold x k a) :=
      sum_le_sum (fun i _ => sub_le_sub_left (threshold_le_level x k a) (x i))
    _ = k := threshold_sum x k a

theorem project_variational (x y : ι → ℚ) (k : ℚ) (hk : 0 < k)
    (hy : ∀ i, 0 ≤ y i) (hys : ∑ i, y i=k) :
    (∑ i, (x i-project x k i)*(y i-project x k i)) ≤ 0 := by
  have hterm : ∀ i, (x i-project x k i-level x k)*(y i-project x k i) ≤ 0 := by
    intro i
    by_cases hi : x i ≤ level x k
    · have hp : project x k i=0 := max_eq_left (sub_nonpos.mpr hi)
      rw [hp,sub_zero,sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi) (hy i)
    · have hp : project x k i=x i-level x k := max_eq_right (sub_nonneg.mpr (le_of_not_ge hi))
      rw [hp]
      have he : x i-(x i-level x k)-level x k=0 := by ring
      rw [he,zero_mul]
  have hh := sum_nonpos (fun i (_ : i ∈ univ) => hterm i)
  have hid : (∑ i, (x i-project x k i-level x k)*(y i-project x k i)) =
      (∑ i, (x i-project x k i)*(y i-project x k i)) := by
    have hz : (∑ i, (y i-project x k i))=0 := by
      rw [sum_sub_distrib,hys,project_sum x k hk,sub_self]
    calc
      _ = ∑ i, ((x i-project x k i)*(y i-project x k i)-
          level x k*(y i-project x k i)) := sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [sum_sub_distrib,← mul_sum,hz,mul_zero,sub_zero]
  rwa [hid] at hh

theorem project_sqdist (x y : ι → ℚ) (k : ℚ) (hk : 0 < k)
    (hy : ∀ i, 0 ≤ y i) (hys : ∑ i, y i=k) :
    (∑ i, (project x k i-y i)^2) ≤ ∑ i, (x i-y i)^2 := by
  have hv := project_variational x y k hk hy hys
  have hs : 0 ≤ ∑ i, (x i-project x k i)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hid : (∑ i, (x i-y i)^2) = (∑ i, (project x k i-y i)^2) +
      (∑ i, (x i-project x k i)^2) -
      2*(∑ i, (x i-project x k i)*(y i-project x k i)) := by
    rw [← sum_add_distrib,mul_sum,← sum_sub_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  linarith

end MetricKMedian.Simplex
end
end

end OAI
