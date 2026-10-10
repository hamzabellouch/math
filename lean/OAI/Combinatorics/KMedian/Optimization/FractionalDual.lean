import Mathlib
import OAI.Combinatorics.KMedian.Geometry.NearestFractional

namespace OAI

section
section
namespace MetricKMedian.FractionalDual
open Finset
variable {ι : Type} [Fintype ι]

def affine (d y : ι → ℚ) (τ : ℚ) : ℚ := τ-∑ i, y i*max 0 (τ-d i)

theorem weak_duality (d y x : ι → ℚ) (τ : ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1) :
    affine d y τ ≤ ∑ i, x i*d i := by
  have ht : ∀ i, τ*x i-y i*max 0 (τ-d i) ≤ x i*d i := by
    intro i
    by_cases hi : τ ≤ d i
    · rw [max_eq_left (sub_nonpos.mpr hi),mul_zero,sub_zero,mul_comm τ]
      exact mul_le_mul_of_nonneg_left hi (hx i).1
    · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hi))]
      have hh := mul_le_mul_of_nonneg_right (hx i).2 (sub_nonneg.mpr (le_of_not_ge hi))
      linarith
  have hs := sum_le_sum (fun i (_ : i ∈ univ) => ht i)
  simpa only [sum_sub_distrib,← mul_sum,hxs,mul_one,affine] using hs

theorem ordered_attains [DecidableEq ι] (d y x : ι → ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1)
    (ho : ∀ i a, 0 < x i → x a < y a → d i ≤ d a) :
    ∃ a, affine d y (d a)=∑ i, x i*d i := by
  let U := univ.filter (fun i => 0 < x i)
  have hU : U.Nonempty := by
    by_contra hn
    have hz : ∀ i, x i=0 := fun i => le_antisymm
      (le_of_not_gt (fun hp => hn ⟨i,mem_filter.mpr ⟨mem_univ _,hp⟩⟩)) (hx i).1
    simp only [hz,sum_const_zero] at hxs
    norm_num at hxs
  obtain ⟨a,ha,hmax⟩ := U.exists_max_image d hU
  refine ⟨a,?_⟩
  have hapos := (mem_filter.mp ha).2
  have hi : ∀ i, y i*max 0 (d a-d i)=x i*(d a-d i) := by
    intro i
    by_cases hl : d i < d a
    · have he : x i=y i := by
        apply le_antisymm (hx i).2
        exact le_of_not_gt (fun hlt => (not_le_of_gt hl) (ho a i hapos hlt))
      rw [he,max_eq_right (sub_nonneg.mpr hl.le)]
    · by_cases he : d i=d a
      · rw [he,sub_self,max_self,mul_zero,mul_zero]
      · have hlt : d a < d i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
        have hz : x i=0 := by
          apply le_antisymm _ (hx i).1
          exact le_of_not_gt (fun hp => (not_le_of_gt hlt)
            (hmax i (mem_filter.mpr ⟨mem_univ _,hp⟩)))
        rw [hz,zero_mul,max_eq_left (sub_nonpos.mpr hlt.le),mul_zero]
  unfold affine
  simp_rw [hi,mul_sub]
  rw [sum_sub_distrib,← sum_mul,hxs,one_mul]
  ring

def thresholds (d : ι → ℚ) (H : ℚ) : Finset ℚ := insert 0 (insert H (univ.image d))

def value (d y : ι → ℚ) (H : ℚ) : ℚ :=
  ((thresholds d H).image (affine d y)).max'
    ((insert_nonempty 0 _).image _)

theorem affine_le_value (d y : ι → ℚ) (H τ : ℚ) (hτ : τ ∈ thresholds d H) :
    affine d y τ ≤ value d y H :=
  le_max' _ _ (mem_image.mpr ⟨τ,hτ,rfl⟩)

theorem value_le_assignment (d y x : ι → ℚ) (H : ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1) :
    value d y H ≤ ∑ i, x i*d i := by
  apply max'_le
  intro q hq
  obtain ⟨τ,_,rfl⟩ := mem_image.mp hq
  exact weak_duality d y x τ hx hxs

theorem value_attained [DecidableEq ι] (d y : ι → ℚ) (H : ℚ)
    (hy : ∀ i, 0 ≤ y i) (hy1 : 1 ≤ ∑ i, y i) :
    ∃ x : ι → ℚ, (∀ i, 0 ≤ x i ∧ x i ≤ y i) ∧ (∑ i, x i)=1 ∧
      (∑ i, x i*d i)=value d y H := by
  obtain ⟨x,_,hx,hs,ho⟩ := Preparation.nearest_fractional univ y d 1
    (fun i _ => hy i) (by norm_num) hy1
  have hx' := fun i => hx i (mem_univ _)
  obtain ⟨a,ha⟩ := ordered_attains d y x hx' hs (fun i a => ho i (mem_univ _) a (mem_univ _))
  refine ⟨x,hx',hs,le_antisymm ?_ (value_le_assignment d y x H hx' hs)⟩
  rw [← ha]
  exact affine_le_value d y H (d a) (by simp [thresholds])

def bestThreshold (d y : ι → ℚ) (H : ℚ) : ℚ :=
  let U := (thresholds d H).filter (fun τ => affine d y τ=value d y H)
  if h : U.Nonempty then U.max' h else 0

theorem bestThreshold_spec (d y : ι → ℚ) (H : ℚ) :
    bestThreshold d y H ∈ thresholds d H ∧
      affine d y (bestThreshold d y H)=value d y H := by
  have hn : ((thresholds d H).filter (fun τ => affine d y τ=value d y H)).Nonempty := by
    obtain ⟨τ,hτ,he⟩ := mem_image.mp (max'_mem ((thresholds d H).image (affine d y))
      ((insert_nonempty 0 _).image _))
    exact ⟨τ,mem_filter.mpr ⟨hτ,he⟩⟩
  simp only [bestThreshold,dite_eq_left hn]
  exact mem_filter.mp (max'_mem _ hn)

def gradient (d y : ι → ℚ) (H : ℚ) (i : ι) : ℚ :=
  -max 0 (bestThreshold d y H-d i)

theorem gradient_spec (d y z : ι → ℚ) (H : ℚ) :
    value d y H-value d z H ≤ ∑ i, gradient d y H i*(y i-z i) := by
  obtain ⟨hτ,he⟩ := bestThreshold_spec d y H
  have hz := affine_le_value d z H (bestThreshold d y H) hτ
  rw [← he]
  have hid : affine d y (bestThreshold d y H)-affine d z (bestThreshold d y H)=
      ∑ i, gradient d y H i*(y i-z i) := by
    unfold affine gradient
    calc
      _ = (∑ i, z i*max 0 (bestThreshold d y H-d i))-
          (∑ i, y i*max 0 (bestThreshold d y H-d i)) := by ring
      _ = ∑ i, (z i*max 0 (bestThreshold d y H-d i)-y i*max 0 (bestThreshold d y H-d i)) := by
        rw [sum_sub_distrib]
      _ = _ := sum_congr rfl (fun _ _ => by ring)
  linarith

theorem gradient_bound (d y : ι → ℚ) (H : ℚ) (hH : 0 ≤ H)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ H) (i : ι) :
    |gradient d y H i| ≤ H := by
  have hmem := (bestThreshold_spec d y H).1
  have hτ : bestThreshold d y H ≤ H := by
    obtain he | hmem := mem_insert.mp hmem
    · rw [he]; exact hH
    · obtain he | hmem := mem_insert.mp hmem
      · exact he.le
      · obtain ⟨a,_,he⟩ := mem_image.mp hmem
        rw [← he]; exact (hd a).2
  unfold gradient
  rw [abs_neg,abs_of_nonneg (le_max_left _ _)]
  exact max_le hH (by linarith [(hd i).1])

end MetricKMedian.FractionalDual
end
end

end OAI
