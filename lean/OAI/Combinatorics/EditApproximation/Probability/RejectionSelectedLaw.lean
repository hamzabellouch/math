import OAI.Combinatorics.EditApproximation.Probability.RejectionSelectedCost

namespace OAI

/-! The independent failure-count/accepted-value representation is exactly
 the law of the literal rejection executions, including discarded trials. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]

def rejectionRuntimeToExecution (execution : RejectionRuntimeArray range) :
    RejectionArrayExecution range := fun i => (execution.1 i, execution.2 i)

def rejectionExecutionToRuntime (execution : RejectionArrayExecution range) :
    RejectionRuntimeArray range := (fun i => (execution i).1, fun i => (execution i).2)

 theorem rejectionRuntimeToExecution_law :
    (rejectionRuntimeArrayLaw range).map (rejectionRuntimeToExecution range) =
      rejectionArrayLaw range := by
  classical
  apply Measure.ext_of_singleton
  intro execution
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : rejectionRuntimeToExecution range ⁻¹' {execution} =
      {rejectionExecutionToRuntime range execution} := by
    ext pair
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply Prod.ext
      · funext i
        exact congrArg (fun x => (x i).1) h
      · funext i
        exact congrArg (fun x => (x i).2) h
    · rintro rfl
      rfl
  rw [hpre]
  change ((Measure.pi (rejectionFailureLaw range)).prod (rejectionAcceptedLaw range))
      {(fun i => (execution i).1, fun i => (execution i).2)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp only [rejectionAcceptedLaw, rejectionArrayLaw, Measure.pi_singleton]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold rejectionArrayCoordinateLaw rejectionExecutionLaw rejectionFailureLaw
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

omit [Fintype ι] [∀ i, NeZero (range i)] in
 theorem rejectionRuntime_roundtrip (execution : RejectionRuntimeArray range) :
    rejectionExecutionToRuntime range (rejectionRuntimeToExecution range execution) = execution := rfl

omit [Fintype ι] [∀ i, NeZero (range i)] in
 theorem rejectionExecution_roundtrip (execution : RejectionArrayExecution range) :
    rejectionRuntimeToExecution range (rejectionExecutionToRuntime range execution) = execution := by
  funext i
  exact Prod.eta (execution i)


/-- Only distinct requested coordinates are sampled. The bound includes
all failed rejection trials, even when the query depends on accepted values. -/
 theorem rejectionRequestedBits_expected_le [DecidableEq ι]
    (program : FiniteQuery ι) (budget : ℕ)
    (hbudget : ∀ accepted : ∀ i, Fin (range i),
      program.cost (fun i => (accepted i).val) (fun i => rejectionBitCount (range i)) ≤ budget) :
    (∫ execution, rejectionSelectedBits range
        (fun i accepted => i ∈ program.keys (fun j => (accepted j).val)) execution
      ∂rejectionRuntimeArrayLaw range) ≤ 2 * (budget : ℝ) := by
  apply rejectionSelectedBits_expected_le
  intro accepted
  have hselected := sum_selected_nat_weights_le
    (program.keys (fun j => (accepted j).val)) (fun i => rejectionBitCount (range i))
  calc
    _ = ∑ i, selectionIndicator (i ∈ program.keys (fun j => (accepted j).val)) *
        (rejectionBitCount (range i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ((program.keys (fun j => (accepted j).val)).map
        (fun i => rejectionBitCount (range i))).sum := hselected
    _ = (program.cost (fun j => (accepted j).val) (fun i => rejectionBitCount (range i)) : ℝ) := by
      rw [FiniteQuery.cost_eq_sum]
    _ ≤ (budget : ℝ) := by exact_mod_cast hbudget accepted

end Law

end EditApproximation

end OAI
