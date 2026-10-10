import OAI.Combinatorics.BalancedRyser.Local.ReuseConditionalSum
import OAI.Combinatorics.BalancedRyser.Local.ReusePrefix

namespace OAI

namespace Balanced.ReuseTower

open PartialAlignment
open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem static_event_probability {Ω : Type*} (μ : PMF Ω)
    (A : Prop) (E : Ω → Prop) :
    (μ.toOuterMeasure {ω | A ∧ E ω}).toReal =
      if A then (μ.toOuterMeasure {ω | E ω}).toReal else 0 := by
  by_cases hA : A
  · simp only [hA, true_and, ite_true]
  · simp [hA]

private theorem exposed_filter_eq (old : Finset (Direction F)) (a : MergedPairs F) :
    (PMF.uniformOfFintype (MergedPairs F)).filter
      {M | expose old M = expose old a} (fiber_supported (expose old) a) =
    (offsetLaw F).filter {M | ∀ d ∈ old, M d = a d}
      (canonical_exposure_supported old a) := by
  have hs : {M | expose old M = expose old a} =
      {M | ∀ d ∈ old, M d = a d} := Set.ext (fun M => expose_eq_iff old M a)
  ext M
  simp only [PMF.filter_apply, hs, offsetLaw_eq_uniform]

private theorem conditional_prescription_probability (pre : List (Prescription F))
    (a : MergedPairs F) (p : Point F) (j : ℕ) (r : Prescription F) :
    (((PMF.uniformOfFintype (MergedPairs F)).filter
      {M | expose (exposedDirections pre) M = expose (exposedDirections pre) a}
      (fiber_supported (expose (exposedDirections pre)) a)).toOuterMeasure
      {M | oldCount pre r = j ∧ prescriptionEvent p r M}).toReal =
    if Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
        (oldGeneratorIndices (Local.decodeTuple r.2) (exposedDirections pre)).card = j then
      (((offsetLaw F).filter {M | ∀ d ∈ exposedDirections pre, M d = a d}
        (canonical_exposure_supported (exposedDirections pre) a)).toOuterMeasure
        {M | (∀ i, OnLine (tuplePoint M (Local.decodeTuple r.2) i)
          (lineThrough r.1.1 p)) ∧
          ∀ i, tuplePoint M (Local.decodeTuple r.2) i ≠ p}).toReal else 0 := by
  rw [exposed_filter_eq]
  have hs : {M : MergedPairs F | oldCount pre r = j ∧ prescriptionEvent p r M} =
      {M | (Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
          (oldGeneratorIndices (Local.decodeTuple r.2) (exposedDirections pre)).card = j) ∧
        ((∀ i, OnLine (tuplePoint M (Local.decodeTuple r.2) i) (lineThrough r.1.1 p)) ∧
          ∀ i, tuplePoint M (Local.decodeTuple r.2) i ≠ p)} := by
    ext M
    simp only [Set.mem_ofPred_eq, prescriptionEvent, oldCount, prescriptionTuple]
    tauto
  rw [hs, static_event_probability]
  split_ifs <;> rfl

theorem conditional_prescription_sum_le (pre : List (Prescription F))
    (hpre : pre.length < 6) (a : MergedPairs F) (p : Point F)
    (j : ℕ) (hj : j ≤ 4) :
    (∑ r : Prescription F,
      (((PMF.uniformOfFintype (MergedPairs F)).filter
        {M | expose (exposedDirections pre) M = expose (exposedDirections pre) a}
        (fiber_supported (expose (exposedDirections pre)) a)).toOuterMeasure
        {M | oldCount pre r = j ∧ prescriptionEvent p r M}).toReal) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * Fintype.card F /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hold : (exposedDirections pre).card ≤ 24 := by
    have h := exposedDirections_card_le pre
    omega
  have h := ReuseConditional.full_code_extension_le (exposedDirections pre) a p j
    hold hj (Fintype.card F) hq.le
  rw [div_self hq.ne'] at h
  simp only [mul_one] at h
  apply le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl (fun r _ => conditional_prescription_probability pre a p j r)

theorem prefixWeight_extension_le (K : ℝ) (hK : 0 ≤ K) (p : Point F)
    (pre : List (Prescription F)) (hpre : pre.length < 6) (j : ℕ) (hj : j ≤ 4) :
    (∑ r : Prescription F, if oldCount pre r = j then prefixWeight K p (r :: pre) else 0) ≤
      ((4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j) * prefixWeight K p pre := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hstep := event_extension_bound
    (expose (exposedDirections pre))
    (fun r M => oldCount pre r = j ∧ prescriptionEvent p r M)
    (prefixEvent p pre)
    ((4 * (4096 * 24 ^ 4) : ℝ) * Fintype.card F /
      (Fintype.card F : ℝ) ^ reuseSaving j)
    (prefixEvent_depends_on_exposed p pre)
    (fun a => conditional_prescription_sum_le pre hpre a p j hj)
  have hevent (r : Prescription F) :
      ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
        {M | prefixEvent p pre M ∧ oldCount pre r = j ∧ prescriptionEvent p r M}).toReal =
      if oldCount pre r = j then Local.offsetProbability (prefixEvent p (r :: pre)) else 0 := by
    by_cases hr : oldCount pre r = j
    · rw [ite_eq_left hr, offsetProbability_eq_uniform]
      congr 2
      ext M
      simp only [hr, true_and, prefixEvent, List.mem_cons, forall_eq_or_imp,
        Set.mem_ofPred_eq, and_comm]
    · rw [ite_eq_right hr]
      have hset : {M | prefixEvent p pre M ∧ oldCount pre r = j ∧ prescriptionEvent p r M} =
          (∅ : Set (MergedPairs F)) := by
        ext M
        simp only [hr, false_and, and_false, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      rw [hset]
      simp
  simp_rw [hevent] at hstep
  rw [← offsetProbability_eq_uniform] at hstep
  calc
    (∑ r : Prescription F, if oldCount pre r = j then prefixWeight K p (r :: pre) else 0) =
        (K / Fintype.card F) ^ (pre.length + 1) *
          ∑ r : Prescription F, if oldCount pre r = j then
            Local.offsetProbability (prefixEvent p (r :: pre)) else 0 := by
      simp only [prefixWeight, List.length_cons, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ (K / Fintype.card F) ^ (pre.length + 1) *
        (((4 * (4096 * 24 ^ 4) : ℝ) * Fintype.card F /
          (Fintype.card F : ℝ) ^ reuseSaving j) *
          Local.offsetProbability (prefixEvent p pre)) :=
      mul_le_mul_of_nonneg_left hstep (pow_nonneg (div_nonneg hK hq.le) _)
    _ = _ := by
      unfold prefixWeight
      rw [pow_succ]
      field_simp

end
end Balanced.ReuseTower

end OAI
