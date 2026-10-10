import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace CylinderConditioning

variable {ι Ω : Type*} [DecidableEq ι]

def avoid (B : ι → Set Ω) (S : Finset ι) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ B i}

omit [DecidableEq ι] in
@[simp] theorem mem_avoid (B : ι → Set Ω) (S : Finset ι) (ω : Ω) :
    ω ∈ avoid B S ↔ ∀ i ∈ S, ω ∉ B i := Iff.rfl

omit [DecidableEq ι] in
@[simp] theorem avoid_empty (B : ι → Set Ω) : avoid B ∅ = Set.univ := by
  ext ω
  simp [avoid]

@[simp] theorem avoid_insert (B : ι → Set Ω) (S : Finset ι) (i : ι) :
    avoid B (insert i S) = avoid B S \ B i := by
  ext ω
  simp [avoid, and_comm]

omit [DecidableEq ι] in
theorem avoid_antitone (B : ι → Set Ω) {S T : Finset ι} (hST : S ⊆ T) :
    avoid B T ⊆ avoid B S := by
  intro ω hω i hi
  exact hω i (hST hi)

theorem product_lower_bound (f : Finset ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, x i ≤ 1)
    (hstep : ∀ S i, i ∉ S → (1 - x i) * f S ≤ f (insert i S))
    (T U : Finset ι) (hdisj : Disjoint T U) :
    f T * ∏ i ∈ U, (1 - x i) ≤ f (T ∪ U) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
      have hiT : i ∉ T := by
        intro hiT
        exact Finset.disjoint_left.mp hdisj hiT (Finset.mem_insert_self _ _)
      have hdisj' : Disjoint T U :=
        Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdisj
      have hiTU : i ∉ T ∪ U := by simp [hiT, hi]
      calc
        f T * ∏ j ∈ insert i U, (1 - x j) =
            (1 - x i) * (f T * ∏ j ∈ U, (1 - x j)) := by
              rw [Finset.prod_insert hi]
              ring
        _ ≤ (1 - x i) * f (T ∪ U) :=
          mul_le_mul_of_nonneg_left (ih hdisj') (sub_nonneg.mpr (hx i))
        _ ≤ f (insert i (T ∪ U)) := hstep _ _ hiTU
        _ = f (T ∪ insert i U) := by rw [Finset.union_insert]

section Measure

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem avoidance_step (B : ι → Set Ω) (x : ι → ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hbound : ∀ S i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S)) :
    ∀ S i, i ∉ S →
      (1 - x i) * μ.real (avoid B S) ≤ μ.real (avoid B (insert i S)) := by
  intro S i hi
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoid B S) (hB i)
  have hle := hbound S i hi
  rw [avoid_insert]
  nlinarith

theorem conditional_event_bound (B : ι → Set Ω) (x : ι → ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hx : ∀ i, x i < 1)
    (hbound : ∀ S i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S))
    (C : Set Ω) (T U : Finset ι) (hdisj : Disjoint T U)
    (hpositive : 0 < μ.real (avoid B (T ∪ U)))
    (hindep : μ.real (C ∩ avoid B T) = μ.real C * μ.real (avoid B T)) :
    μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
      μ.real C * ∏ i ∈ U, (1 - x i)⁻¹ := by
  have hprod : 0 < ∏ i ∈ U, (1 - x i) :=
    Finset.prod_pos fun i _ => sub_pos.mpr (hx i)
  have hlower := product_lower_bound (fun S => μ.real (avoid B S)) x
    (fun i => (hx i).le) (avoidance_step μ B x hB hbound) T U hdisj
  have hbase : μ.real (avoid B T) ≤
      μ.real (avoid B (T ∪ U)) / (∏ i ∈ U, (1 - x i)) :=
    (le_div_iff₀ hprod).2 hlower
  have hnum : μ.real (C ∩ avoid B (T ∪ U)) ≤
      μ.real C * μ.real (avoid B T) := by
    rw [← hindep]
    exact measureReal_mono (Set.inter_subset_inter_right C
      (avoid_antitone B Finset.subset_union_left))
  apply (div_le_iff₀ hpositive).2
  calc
    μ.real (C ∩ avoid B (T ∪ U)) ≤ μ.real C * μ.real (avoid B T) := hnum
    _ ≤ μ.real C *
        (μ.real (avoid B (T ∪ U)) / ∏ i ∈ U, (1 - x i)) :=
      mul_le_mul_of_nonneg_left hbase measureReal_nonneg
    _ = (μ.real C * ∏ i ∈ U, (1 - x i)⁻¹) *
        μ.real (avoid B (T ∪ U)) := by
      rw [Finset.prod_inv_distrib]
      ring

end Measure
end CylinderConditioning
end Balanced

end OAI
