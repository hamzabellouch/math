import Mathlib
import OAI.Combinatorics.KMedian.Optimization.TruncatedObjective

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def nearWeight (d x : κ → ι → ℚ) (j : κ) (i : ι) : ℚ :=
  if d j i ≤ 1 then x j i else 0

def nearMass (d x : κ → ι → ℚ) (j : κ) : ℚ := ∑ i, nearWeight d x j i

def repairedOpening (y : ι → ℚ) (ρ : ℚ) (i : ι) : ℚ := min 1 (y i/(1-ρ))

def repairedAssignment (d x : κ → ι → ℚ) (j : κ) (i : ι) : ℚ :=
  nearWeight d x j i/nearMass d x j

omit [Fintype ι] [Fintype κ] in
theorem nearWeight_nonneg (d x : κ → ι → ℚ) (hx : ∀ j i, 0 ≤ x j i) (j : κ) (i : ι) :
    0 ≤ nearWeight d x j i := by
  unfold nearWeight
  split_ifs
  · exact hx j i
  · exact le_rfl

omit [Fintype ι] [Fintype κ] in
theorem nearWeight_le (d x : κ → ι → ℚ) (hx : ∀ j i, 0 ≤ x j i) (j : κ) (i : ι) :
    nearWeight d x j i ≤ x j i := by unfold nearWeight; split_ifs <;> simp_all

theorem nearMass_lower (d x : κ → ι → ℚ) (H ρ : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (hx : ∀ j i, 0 ≤ x j i)
    (hs : ∀ j, ∑ i, x j i=1)
    (hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ ρ*H) (j : κ) :
    1-ρ ≤ nearMass d x j := by
  classical
  have hc : ∀ j, 0 ≤ ∑ i, x j i*truncated d H j i := fun j =>
    sum_nonneg (fun i _ => mul_nonneg (hx j i) (truncated_bounds d H hH hd j i).1)
  have hterm : ∀ i, H*(x j i-nearWeight d x j i) ≤ x j i*truncated d H j i := by
    intro i
    unfold nearWeight truncated
    split_ifs
    · simpa only [sub_self,mul_zero] using mul_nonneg (hx j i) (hd j i)
    · simp only [sub_zero]; exact (mul_comm _ _).le
  have hf : H*(1-nearMass d x j) ≤ ρ*H := by
    calc
      _ = ∑ i, H*(x j i-nearWeight d x j i) := by
        rw [← mul_sum,sum_sub_distrib,hs]; rfl
      _ ≤ ∑ i, x j i*truncated d H j i := sum_le_sum (fun i _ => hterm i)
      _ ≤ ∑ j, ∑ i, x j i*truncated d H j i := single_le_sum (fun j _ => hc j) (mem_univ j)
      _ ≤ _ := hcost
  nlinarith

theorem repaired_spec (d x : κ → ι → ℚ) (y : ι → ℚ) (H ρ k : ℚ)
    (hH : 1 ≤ H) (hρ : ρ < 1) (hkρ : ρ*(k+1) ≤ 1)
    (hd : ∀ j i, 0 ≤ d j i) (hy : ∀ i, 0 ≤ y i)
    (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ y i)
    (hs : ∀ j, ∑ i, x j i=1) (hybudget : ∑ i, y i ≤ k)
    (hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ ρ*H) :
    (∀ i, 0 ≤ repairedOpening y ρ i ∧ repairedOpening y ρ i ≤ 1) ∧
    (∀ j i, 0 ≤ repairedAssignment d x j i ∧
      repairedAssignment d x j i ≤ repairedOpening y ρ i) ∧
    (∀ j, ∑ i, repairedAssignment d x j i=1) ∧
    (∑ i, repairedOpening y ρ i) ≤ k+1 ∧
    (∑ j, ∑ i, repairedAssignment d x j i*d j i) ≤
      (∑ j, ∑ i, x j i*truncated d H j i)/(1-ρ) := by
  classical
  have hρp : 0 < 1-ρ := sub_pos.mpr hρ
  have hx0 : ∀ j i, 0 ≤ x j i := fun j i => (hx j i).1
  have hm : ∀ j, 1-ρ ≤ nearMass d x j := nearMass_lower d x H ρ hH hd hx0 hs hcost
  have hmp : ∀ j, 0 < nearMass d x j := fun j => hρp.trans_le (hm j)
  have hw : ∀ j i, 0 ≤ nearWeight d x j i := nearWeight_nonneg d x hx0
  have hwy : ∀ j i, nearWeight d x j i ≤ y i := fun j i =>
    (nearWeight_le d x hx0 j i).trans (hx j i).2
  have hwm : ∀ j i, nearWeight d x j i ≤ nearMass d x j := fun j i =>
    single_le_sum (fun a _ => hw j a) (mem_univ i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨le_min (by norm_num) (div_nonneg (hy i) hρp.le),min_le_left _ _⟩
  · intro j i
    refine ⟨div_nonneg (hw j i) (hmp j).le,le_min ?_ ?_⟩
    · exact (div_le_one (hmp j)).mpr (hwm j i)
    · calc
        _ ≤ nearWeight d x j i/(1-ρ) := div_le_div_of_nonneg_left (hw j i) hρp (hm j)
        _ ≤ _ := div_le_div_of_nonneg_right (hwy j i) hρp.le
  · intro j
    simp only [repairedAssignment,← sum_div]
    exact div_self (hmp j).ne'
  · calc
      _ ≤ ∑ i, y i/(1-ρ) := sum_le_sum (fun _ _ => min_le_right _ _)
      _ = (∑ i, y i)/(1-ρ) := (sum_div _ _ _).symm
      _ ≤ k/(1-ρ) := div_le_div_of_nonneg_right hybudget hρp.le
      _ ≤ k+1 := (div_le_iff₀ hρp).mpr (by nlinarith)
  · have hterm : ∀ j i, repairedAssignment d x j i*d j i ≤ x j i*truncated d H j i/(1-ρ) := by
      intro j i
      have hc : nearWeight d x j i*d j i ≤ x j i*truncated d H j i := by
        unfold nearWeight truncated
        split_ifs
        · exact le_rfl
        · simpa only [zero_mul] using mul_nonneg (hx0 j i) (by linarith : 0 ≤ H)
      calc
        _ = (nearWeight d x j i*d j i)/nearMass d x j := by unfold repairedAssignment; ring
        _ ≤ (nearWeight d x j i*d j i)/(1-ρ) :=
          div_le_div_of_nonneg_left (mul_nonneg (hw j i) (hd j i)) hρp (hm j)
        _ ≤ _ := div_le_div_of_nonneg_right hc hρp.le
    calc
      _ ≤ ∑ j, ∑ i, x j i*truncated d H j i/(1-ρ) :=
        sum_le_sum (fun j _ => sum_le_sum (fun i _ => hterm j i))
      _ = _ := by simp only [← sum_div]

end MetricKMedian.TruncatedLP
end
end

end OAI
