import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoWork
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A first request can depend on earlier answers, but cannot depend on
its own unexposed coordinate. Finite product independence then preserves
that coordinate's unconditional expected cost. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory Finset

attribute [local instance] Classical.propDecidable



namespace FiniteQuery

/-- Changing an oracle only at `key` does not change whether `key` is
requested. The two executions agree up to its first request. -/
theorem mem_keys_iff_of_agree_off {ι : Type*} [DecidableEq ι]
    (left right : ι → ℚ) (key : ι)
    (hagrees : ∀ other, other ≠ key → left other = right other)
    (query : FiniteQuery ι) : key ∈ query.keys left ↔ key ∈ query.keys right := by
  induction query with
  | done value => rfl
  | read first next ih =>
    by_cases heq : first = key
    · subst first
      simp only [keys, List.mem_cons, true_or]
    · have hvalue := hagrees first heq
      simp only [keys, List.mem_cons, Ne.symm heq, false_or, hvalue]
      exact ih (right first)

end FiniteQuery

theorem sum_distinct_requests_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, if i ∈ keys then weight i else 0) ≤ (keys.map weight).sum := by
  have hset : univ.filter (fun i => i ∈ keys) = keys.toFinset := by ext i; simp
  rw [← sum_filter, hset]
  clear hset
  induction keys with
  | nil => simp
  | cons key keys ih =>
    by_cases hmem : key ∈ keys
    · simp only [List.toFinset_cons, insert_eq_of_mem (List.mem_toFinset.mpr hmem),
        List.map_cons, List.sum_cons]
      omega
    · rw [List.toFinset_cons, sum_insert (by simpa only [List.mem_toFinset] using hmem),
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

theorem sum_selected_nat_weights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, selectionIndicator (i ∈ keys) * (weight i : ℝ)) ≤
      ((keys.map weight).sum : ℕ) := by
  calc
    _ = ∑ i, if i ∈ keys then (weight i : ℝ) else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ keys <;> simp [selectionIndicator, hi]
    _ ≤ _ := by exact_mod_cast sum_distinct_requests_le keys weight

section IndependentCost

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
  (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Selection stable under replacing its own coordinate is independent
of that coordinate. No accuracy event is used. -/
theorem fresh_coordinate_independent (i : ι) (selected : (∀ j, X j) → Prop)
    (hstable : ∀ left right : ∀ j, X j,
      (∀ j, j ≠ i → left j = right j) → (selected left ↔ selected right))
    (cost : X i → ℝ) :
    IndepFun (fun draw => selectionIndicator (selected draw))
      (fun draw => cost (draw i)) (Measure.pi μ) := by
  classical
  let S : Finset ι := univ.erase i
  let restore : (∀ j : S, X j) → ∀ j, X j := fun rest j =>
    if h : j = i then h.symm ▸ Classical.choice (inferInstance : Nonempty (X i))
    else rest ⟨j, by simp [S, h]⟩
  let choose : (∀ j : S, X j) → ℝ := fun rest => selectionIndicator (selected (restore rest))
  let charge : (∀ j : ({i} : Finset ι), X j) → ℝ := fun rest => cost (rest ⟨i, by simp⟩)
  have hrestore (draw : ∀ j, X j) : selected (restore (fun j : S => draw j)) ↔ selected draw := by
    apply hstable
    intro j hj
    dsimp only [restore]
    rw [dite_eq_right hj]
  have hind := (iIndepFun_pi (μ := μ) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)).indepFun_finset S {i} (by simp [S])
      (fun _ => measurable_pi_apply _)
  have hcomp := hind.comp (measurable_of_finite choose) (measurable_of_finite charge)
  convert hcomp using 1
  · ext draw
    exact congrArg selectionIndicator (propext (hrestore draw).symm)
  · rfl

theorem fresh_coordinate_expected_cost (i : ι) (selected : (∀ j, X j) → Prop)
    (hstable : ∀ left right : ∀ j, X j,
      (∀ j, j ≠ i → left j = right j) → (selected left ↔ selected right))
    (cost : X i → ℝ) :
    (∫ draw, (selectionIndicator (selected draw)) * cost (draw i) ∂Measure.pi μ) =
      (∫ draw, (selectionIndicator (selected draw)) ∂Measure.pi μ) *
        (∫ value, cost value ∂μ i) := by
  classical
  rw [(fresh_coordinate_independent μ i selected hstable cost).integral_fun_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable]
  rw [integral_comp_eval (measurable_of_finite cost).aestronglyMeasurable]

/-- Summing the first-request charges costs at most the expected selected
width budget times the common per-width cost. -/
theorem fresh_coordinates_expected_sum_le
    (selected : ι → (∀ j, X j) → Prop)
    (hstable : ∀ i left right,
      (∀ j, j ≠ i → left j = right j) → (selected i left ↔ selected i right))
    (cost : (i : ι) → X i → ℝ) (width : ι → ℝ) (overhead budget : ℝ)
    (hoverhead : 0 ≤ overhead)
    (hcost : ∀ i, (∫ value, cost i value ∂μ i) ≤ width i * overhead)
    (hbudget : ∀ draw, ∑ i, (selectionIndicator (selected i draw)) * width i ≤ budget) :
    (∫ draw, ∑ i, (selectionIndicator (selected i draw)) * cost i (draw i) ∂Measure.pi μ) ≤
      budget * overhead := by
  classical
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [fresh_coordinate_expected_cost μ _ _ (hstable _) (cost _)]
  calc
    _ ≤ ∑ i, (∫ draw, (selectionIndicator (selected i draw)) ∂Measure.pi μ) *
        (width i * overhead) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcost i) (integral_nonneg fun draw => by unfold selectionIndicator; split_ifs <;> norm_num)
    _ = (∫ draw, ∑ i, (selectionIndicator (selected i draw)) * width i ∂Measure.pi μ) * overhead := by
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite), sum_mul]
      apply sum_congr rfl
      intro i _
      rw [integral_mul_const]
      ring
    _ ≤ budget * overhead := by
      apply mul_le_mul_of_nonneg_right _ hoverhead
      exact (integral_mono (Integrable.of_finite) (integrable_const _) hbudget).trans_eq (by simp)

/-- Concrete specialization to a finite adaptive read program. A key is
charged once even if later continuation code requests it repeatedly. -/
theorem finiteQuery_fresh_expected_cost_le (query : FiniteQuery ι)
    (answer : (i : ι) → X i → ℚ) (cost : (i : ι) → X i → ℝ)
    (width : ι → ℝ) (overhead budget : ℝ) (hoverhead : 0 ≤ overhead)
    (hcost : ∀ i, (∫ value, cost i value ∂μ i) ≤ width i * overhead)
    (hbudget : ∀ draw : ∀ j, X j,
      ∑ i, (selectionIndicator (i ∈ query.keys (fun j => answer j (draw j)))) * width i ≤ budget) :
    (∫ draw, ∑ i,
      (selectionIndicator (i ∈ query.keys (fun j => answer j (draw j)))) * cost i (draw i)
        ∂Measure.pi μ) ≤ budget * overhead := by
  apply fresh_coordinates_expected_sum_le μ
    (fun i (draw : ∀ j, X j) => i ∈ query.keys (fun j => answer j (draw j)))
    _ cost width overhead budget hoverhead hcost hbudget
  intro i left right hagree
  exact FiniteQuery.mem_keys_iff_of_agree_off _ _ i
    (fun j hj => congrArg (answer j) (hagree j hj)) query

end IndependentCost

end EditApproximation

end OAI
