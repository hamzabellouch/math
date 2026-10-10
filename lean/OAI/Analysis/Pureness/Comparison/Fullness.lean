import OAI.Analysis.Pureness.Comparison.FaithfulTrace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Sequences
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace OAI
open Filter Topology
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A]

def finiteSandwichIdeal (e : A) : TwoSidedIdeal A :=
  .mk' {a | ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = a}
    ⟨[], by simp⟩
    (by rintro a b ⟨l, rfl⟩ ⟨m, rfl⟩; exact ⟨l ++ m, by simp⟩)
    (by
      rintro a ⟨l, rfl⟩
      refine ⟨l.map (fun v => (-v.1, v.2)), ?_⟩
      simp only [List.map_map, Function.comp_def, neg_mul]
      induction l with
      | nil => simp
      | cons v l ih => simp [ih, add_comm])
    (by
      rintro a b ⟨l, rfl⟩
      refine ⟨l.map (fun v => (a * v.1, v.2)), ?_⟩
      simp only [List.map_map, Function.comp_def, mul_assoc]
      induction l with
      | nil => simp
      | cons v l ih => simpa [mul_add, mul_assoc] using congrArg (fun z => a * v.1 * e * v.2 + z) ih)
    (by
      rintro a b ⟨l, rfl⟩
      refine ⟨l.map (fun v => (v.1, v.2 * b)), ?_⟩
      simp only [List.map_map, Function.comp_def, ← mul_assoc]
      induction l with
      | nil => simp
      | cons v l ih => simpa [add_mul, mul_assoc] using congrArg (fun z => v.1 * e * v.2 * b + z) ih)

@[simp] theorem mem_finiteSandwichIdeal (e a : A) :
    a ∈ finiteSandwichIdeal e ↔
      ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = a := by
  simp [finiteSandwichIdeal]

def closedTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  .mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (by
      intro a b ha hb
      obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp ha
      obtain ⟨y, hy, hyt⟩ := mem_closure_iff_seq_limit.mp hb
      exact mem_closure_of_tendsto (hxt.add hyt)
        (Eventually.of_forall fun n => I.add_mem (hx n) (hy n)))
    (by
      intro a ha
      obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp ha
      exact mem_closure_of_tendsto hxt.neg
        (Eventually.of_forall fun n => I.neg_mem (hx n)))
    (by
      intro a b hb
      obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp hb
      exact mem_closure_of_tendsto (hxt.const_mul a)
        (Eventually.of_forall fun n => I.mul_mem_left a (x n) (hx n)))
    (by
      intro a b ha
      obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp ha
      exact mem_closure_of_tendsto (hxt.mul_const b)
        (Eventually.of_forall fun n => I.mul_mem_right (x n) b (hx n)))

@[simp] theorem coe_closedTwoSidedIdeal (I : TwoSidedIdeal A) :
    (closedTwoSidedIdeal I : Set A) = closure (I : Set A) := by
  simp [closedTwoSidedIdeal]

theorem full_of_ne_zero [IsSimpleCStarAlgebra A] {e : A} (he : e ≠ 0) :
    closure (finiteSandwichIdeal e : Set A) = Set.univ := by
  have hem : e ∈ finiteSandwichIdeal e :=
    (mem_finiteSandwichIdeal e e).mpr ⟨[(1, 1)], by simp⟩
  rcases IsSimpleCStarAlgebra.eq_bot_or_eq_top
      (closedTwoSidedIdeal (finiteSandwichIdeal e))
      (by simp)
      with h | h
  · have hz : e ∈ (⊥ : TwoSidedIdeal A) := by
      rw [← h]
      simpa [closedTwoSidedIdeal] using (subset_closure hem : e ∈ closure (finiteSandwichIdeal e : Set A))
    exact (he (by simpa using hz)).elim
  · simp only [← coe_closedTwoSidedIdeal, h, TwoSidedIdeal.coe_top]

theorem exists_finite_fullness_approximation [IsSimpleCStarAlgebra A]
    {e : A} (he : e ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (A × A), ‖1 - (l.map fun v => v.1 * e * v.2).sum‖ < ε := by
  have h : (1 : A) ∈ closure (finiteSandwichIdeal e : Set A) := by
    rw [full_of_ne_zero he]; trivial
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨l, rfl⟩ := (mem_finiteSandwichIdeal e s).mp hs
  exact ⟨l, by simpa only [dist_eq_norm] using hdist⟩

theorem exists_finite_fullness_identity [IsSimpleCStarAlgebra A]
    {e : A} (he : e ≠ 0) :
    ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = 1 := by
  obtain ⟨l, hl⟩ := exists_finite_fullness_approximation he (ε := 1) zero_lt_one
  let s := (l.map fun v => v.1 * e * v.2).sum
  have hs : s ∈ finiteSandwichIdeal e := (mem_finiteSandwichIdeal e s).mpr ⟨l, rfl⟩
  have hu : IsUnit s := by
    have := (Units.oneSub (1 - s) (by exact hl)).isUnit
    change IsUnit (1 - (1 - s)) at this
    simpa only [sub_sub_cancel] using this
  obtain ⟨u, hu⟩ := hu
  have hone := (finiteSandwichIdeal e).mul_mem_left (↑(u⁻¹) : A) s hs
  rw [← hu, Units.inv_mul] at hone
  exact (mem_finiteSandwichIdeal e 1).mp hone

theorem exists_nonzero_sandwich [IsSimpleCStarAlgebra A]
    {c d : A} (hc : c ≠ 0) (hd : d ≠ 0) : ∃ y : A, c * y * d ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ∀ s ∈ finiteSandwichIdeal d, c * s = 0 := by
    intro s hs
    obtain ⟨l, rfl⟩ := (mem_finiteSandwichIdeal d s).mp hs
    clear hs
    induction l with
    | nil => simp
    | cons v l ih => simp only [List.map_cons, List.sum_cons, mul_add, ← mul_assoc,
        h v.1, zero_mul, ih, zero_add]
  have hone : (1 : A) ∈ closure (finiteSandwichIdeal d : Set A) := by
    rw [full_of_ne_zero hd]; trivial
  obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp hone
  have ht := hxt.const_mul c
  have hzero : Tendsto (fun n => c * x n) atTop (𝓝 0) := by
    simpa only [funext (fun n => hz (x n) (hx n))] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : A)) atTop (𝓝 0))
  exact hc (by simpa using tendsto_nhds_unique ht hzero)

end CuntzComparison

end OAI
