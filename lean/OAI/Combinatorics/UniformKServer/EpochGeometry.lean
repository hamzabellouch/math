import Mathlib
import OAI.Combinatorics.UniformKServer.AllocationEpoch

namespace OAI

                                    
section

/-! Actual held vector epochs and persistent dominant identity of companion §03.
 The scalar cumulative-credit budget is linked by an exact projection. -/
noncomputable section
namespace UniformKServer.EpochGeometry
open Finset
variable {ι : Type*} [Fintype ι]

def total (a : ι → ℝ) : ℝ := ∑ i, a i
def variation (a b : ι → ℝ) : ℝ := ∑ i, |b i-a i|
def side (o : ι) (a : ι → ℝ) : ℝ := by
  classical
  exact ∑ i, if i=o then 0 else a i

structure State (ι : Type*) where
  base : ι → ℝ
  credit : ℝ

def initial (a : ι → ℝ) : State ι := ⟨a,0⟩
def scalar (s : State ι) : AllocationEpoch.State := ⟨total s.base,s.credit⟩
def valid (a : ι → ℝ) (s : State ι) : Prop :=
  (∀ i, 0 ≤ s.base i) ∧ 0 ≤ s.credit ∧ s.credit ≤ total s.base/100 ∧
    variation s.base a ≤ s.credit

def update (s : State ι) (a b : ι → ℝ) (parent : Bool) : State ι := by
  classical
  exact if AllocationEpoch.fires (scalar s) (variation a b) parent then initial b
    else ⟨s.base,s.credit+variation a b⟩

def dominant (s : State ι) : Option ι := by
  classical
  exact if h : ∃ i, 0 < total s.base ∧ (85/100)*total s.base ≤ s.base i
    then some h.choose else none

theorem variation_nonneg (a b : ι → ℝ) : 0 ≤ variation a b := sum_nonneg fun i _ => abs_nonneg (b i-a i)
theorem variation_self (a : ι → ℝ) : variation a a=0 := by simp [variation]
theorem variation_triangle (a b c : ι → ℝ) : variation a c ≤ variation a b+variation b c := by
  unfold variation
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  calc
    |c i-a i| = |(b i-a i)+(c i-b i)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

theorem total_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) : 0 ≤ total a := sum_nonneg fun i _ => ha i

theorem total_difference (a b : ι → ℝ) : |total b-total a| ≤ variation a b := by
  rw [total,total,←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem initial_valid {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) : valid a (initial a) := by
  refine ⟨ha,le_rfl,?_,?_⟩
  · exact div_nonneg (total_nonneg ha) (by norm_num)
  · simp [initial,variation_self]

theorem scalar_valid {a : ι → ℝ} {s : State ι} (hs : valid a s) :
    AllocationEpoch.valid (total a) (scalar s) :=
  ⟨total_nonneg hs.1,hs.2.1,hs.2.2.1,(total_difference s.base a).trans hs.2.2.2⟩

theorem update_valid {a b : ι → ℝ} {s : State ι} (hs : valid a s)
    (hb : ∀ i, 0 ≤ b i) (parent : Bool) : valid b (update s a b parent) := by
  unfold update
  split
  · exact initial_valid hb
  · rename_i h
    have hh : s.credit+variation a b ≤ total s.base/100 :=
      le_of_not_gt (fun hh => h (Or.inr hh))
    exact ⟨hs.1,add_nonneg hs.2.1 (variation_nonneg a b),hh,
      (variation_triangle s.base a b).trans (by linarith [hs.2.2.2])⟩

theorem scalar_update (s : State ι) (a b : ι → ℝ) (parent : Bool) :
    scalar (update s a b parent) = AllocationEpoch.update (scalar s) (total b) (variation a b) parent := by
  classical
  unfold update AllocationEpoch.update
  split <;> rfl

def schedule (a : ℕ → ι → ℝ) (parent : ℕ → Bool) : ℕ → State ι
  | 0 => initial (a 0)
  | t+1 => update (schedule a parent t) (a t) (a (t+1)) (parent t)

theorem schedule_valid {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (parent : ℕ → Bool) :
    ∀ t, valid (a t) (schedule a parent t) := by
  intro t
  induction t with
  | zero => exact initial_valid (ha 0)
  | succ t ih => exact update_valid ih (ha (t+1)) (parent t)

theorem scalar_schedule (a : ℕ → ι → ℝ) (parent : ℕ → Bool) : ∀ t,
    scalar (schedule a parent t) = AllocationEpoch.schedule (fun t => total (a t))
      (fun t => variation (a t) (a (t+1))) parent t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [schedule,scalar_update,AllocationEpoch.schedule,ih]

theorem wholesale_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (parent : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, AllocationEpoch.charge (scalar (schedule a parent t))
      (total (a t)) (total (a (t+1))) (variation (a t) (a (t+1))) (parent t)) ≤
      203*(∑ t ∈ range H, variation (a t) (a (t+1)))+
        ∑ t ∈ range H, (if parent t then total (a t)+total (a (t+1)) else 0) := by
  simp_rw [scalar_schedule]
  exact AllocationEpoch.schedule_budget (fun t => total_nonneg (ha t))
    (fun t => total_difference (a t) (a (t+1))) parent H

theorem coordinate_difference (a b : ι → ℝ) (i : ι) : |b i-a i| ≤ variation a b :=
  by
  unfold variation
  exact single_le_sum (fun j _ => abs_nonneg (b j-a j)) (mem_univ i)

theorem side_difference (a b : ι → ℝ) (o : ι) : |side o b-side o a| ≤ variation a b := by
  classical
  unfold side variation
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  apply sum_le_sum
  intro i _
  by_cases h : i=o
  · simp [h]
  · simp [h]

theorem total_with_side (a : ι → ℝ) (o : ι) : total a = a o+side o a := by
  classical
  unfold total side
  have he : (∑ i : ι, if i=o then a i else 0)=a o := by simp
  rw [←he,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem dominant_spec {s : State ι} {o : ι} (ho : dominant s=some o) :
    0 < total s.base ∧ (85/100)*total s.base ≤ s.base o := by
  classical
  unfold dominant at ho
  split at ho
  · rename_i h
    have he := Option.some.inj ho
    rw [←he]
    exact h.choose_spec
  · contradiction

theorem absent_spec {s : State ι} (ho : dominant s=none) (i : ι) :
    ¬(0 < total s.base ∧ (85/100)*total s.base ≤ s.base i) := by
  classical
  unfold dominant at ho
  split at ho
  · contradiction
  · rename_i h
    exact fun hi => h ⟨i,hi⟩

theorem two_le_total {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {i j : ι} (hij : i ≠ j) :
    a i+a j ≤ total a := by
  classical
  have h : ∑ r ∈ ({i,j} : Finset ι), a r ≤ total a :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun r _ _ => ha r)
  simpa [sum_pair hij] using h

theorem regular_base {s : State ι} (hs : ∀ i, 0 ≤ s.base i) {i : ι}
    (hi : dominant s ≠ some i) : s.base i ≤ (85/100)*total s.base := by
  have ht := total_nonneg hs
  cases ho : dominant s with
  | none =>
    by_cases hp : 0 < total s.base
    · exact (not_le.mp (fun h => absent_spec ho i ⟨hp,h⟩)).le
    · have hle : s.base i ≤ total s.base := single_le_sum (fun j _ => hs j) (mem_univ i)
      linarith
  | some o =>
    have hij : i ≠ o := by rintro rfl; exact hi ho
    have hdom := dominant_spec ho
    have hsum := two_le_total hs hij
    linarith

theorem regular_size {s : State ι} {a : ι → ℝ} (hs : valid a s) {i : ι}
    (hi : dominant s ≠ some i) : a i ≤ (86/100)*total s.base := by
  have hb := regular_base hs.1 hi
  have hd := coordinate_difference s.base a i
  have hpos := le_abs_self (a i-s.base i)
  linarith [hs.2.2.1,hs.2.2.2]

theorem dominant_size {s : State ι} {a : ι → ℝ} (hs : valid a s) {o : ι}
    (ho : dominant s=some o) : (84/100)*total s.base ≤ a o ∧
      side o a ≤ (16/100)*total s.base := by
  have hb := dominant_spec ho
  have hd := coordinate_difference s.base a o
  have hneg := neg_le_abs (a o-s.base o)
  have hsides := side_difference s.base a o
  have hside := le_abs_self (side o a-side o s.base)
  have htotal := total_with_side s.base o
  constructor <;> linarith [hs.2.2.1,hs.2.2.2]

theorem total_comparison {s : State ι} {a : ι → ℝ} (hs : valid a s) :
    (99/100)*total s.base ≤ total a ∧ total a ≤ (101/100)*total s.base := by
  have h := abs_le.mp ((total_difference s.base a).trans hs.2.2.2)
  constructor <;> linarith [hs.2.2.1]

end UniformKServer.EpochGeometry

end


end

end OAI
