import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

/-! Actual finite lower-envelope masks for the common-point trace argument.
The variation is paid only on intervals in which the corresponding cutoff
is active. These estimates precede the Sobolev and infinite-mask limits. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 def finiteTraceMask {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => min (finiteTraceMask cutoff I x t n) (if t ∈ I n then cutoff n x else 1)

 theorem finiteTraceMask_bounds {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (t : ℝ) (n : ℕ) :
    finiteTraceMask cutoff I x t n ∈ Icc (0:ℝ) 1 := by
  induction n with
  | zero => exact ⟨zero_le_one,le_rfl⟩
  | succ n ih =>
    simp only [finiteTraceMask,mem_Icc]
    constructor
    · apply le_min ih.1
      split_ifs
      · exact (hcutoff n x).1
      · exact zero_le_one
    · exact (min_le_left _ _).trans ih.2

 theorem finiteTraceMask_antitone {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : Antitone (finiteTraceMask cutoff I x t) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

 theorem finiteTraceMask_eq_one {X : Type*} {cutoff : ℕ → X → ℝ} {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {n : ℕ} (h : ∀ j < n, t ∈ I j → cutoff j x = 1) :
    finiteTraceMask cutoff I x t n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finiteTraceMask,ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    by_cases ht : t ∈ I n
    · rw [ite_eq_left ht,h n (Nat.lt_succ_self n) ht,min_self]
    · rw [ite_eq_right ht,min_self]

 theorem finiteTraceMask_le_active {X : Type*} {cutoff : ℕ → X → ℝ} {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j n : ℕ} (hj : j < n) (ht : t ∈ I j) :
    finiteTraceMask cutoff I x t n ≤ cutoff j x := by
  have he : finiteTraceMask cutoff I x t (j+1) ≤ cutoff j x := by
    simpa only [finiteTraceMask,ite_eq_left ht] using
      min_le_right (finiteTraceMask cutoff I x t j) (cutoff j x)
  exact ((finiteTraceMask_antitone cutoff I x t) hj).trans he

 theorem finiteTraceMask_zero_of_active {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j n : ℕ} (hj : j < n) (ht : t ∈ I j) (hz : cutoff j x = 0) :
    finiteTraceMask cutoff I x t n = 0 := by
  apply le_antisymm
  · simpa only [hz] using finiteTraceMask_le_active (cutoff := cutoff) (x := x) hj ht
  · exact (finiteTraceMask_bounds hcutoff I x t n).1

 theorem finiteTraceMask_variation {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x y : X) (t : ℝ) (n : ℕ) :
    |finiteTraceMask cutoff I x t n-finiteTraceMask cutoff I y t n| ≤
      ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) t := by
  induction n with
  | zero => simp [finiteTraceMask]
  | succ n ih =>
    have hs : 0 ≤ ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) t :=
      Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => abs_nonneg _) t)
    rw [finiteTraceMask,finiteTraceMask,Finset.sum_range_succ]
    have hh := abs_min_sub_min_le_max (finiteTraceMask cutoff I x t n)
      (if t ∈ I n then cutoff n x else 1) (finiteTraceMask cutoff I y t n)
      (if t ∈ I n then cutoff n y else 1)
    apply hh.trans
    apply max_le
    · apply ih.trans
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => abs_nonneg _) _)
    · by_cases ht : t ∈ I n
      · simp only [ite_eq_left ht,indicator_of_mem ht]
        exact le_add_of_nonneg_left hs
      · simp only [ite_eq_right ht,sub_self,abs_zero,indicator_of_notMem ht,add_zero]
        exact hs

 theorem finiteTraceMask_measurable {X : Type*} (cutoff : ℕ → X → ℝ) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) :
    Measurable (fun t => finiteTraceMask cutoff I x t n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.min (Measurable.ite (hI n) measurable_const measurable_const)

 def infiniteTraceMask {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : ℝ := ⨅ n, finiteTraceMask cutoff I x t n

 theorem finiteTraceMask_tendsto {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (t : ℝ) :
    Tendsto (finiteTraceMask cutoff I x t) atTop (𝓝 (infiniteTraceMask cutoff I x t)) := by
  apply tendsto_atTop_ciInf (finiteTraceMask_antitone cutoff I x t)
  exact ⟨0,fun _ ⟨n,hn⟩ => hn ▸ (finiteTraceMask_bounds hcutoff I x t n).1⟩

end CircleDomainRigidity

end

end OAI
