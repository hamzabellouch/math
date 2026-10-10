import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.ReuseGlobalExtension

namespace OAI

namespace Balanced.ReuseConditional

open PartialAlignment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem sum_slot_tuple (f : Local.TupleCode F → Direction F → ℝ) :
    (∑ r : Slot F × Local.TupleCode F, f r.2 r.1.1) =
      2 * ∑ c : Local.TupleCode F, ∑ g : Direction F, f c g := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Slot, Fintype.sum_prod_type, Fintype.sum_bool, ← two_mul]
  simp only [← Finset.mul_sum]

theorem full_code_extension_le (old : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) (j : ℕ) (hold : old.card ≤ 24) (hj : j ≤ 4)
    (K : ℝ) (hK : 0 ≤ K) :
    (∑ r : Slot F × Local.TupleCode F,
      if Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
          (oldGeneratorIndices (Local.decodeTuple r.2) old).card = j then
        (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
          (canonical_exposure_supported old a)).toOuterMeasure
          {M | (∀ i, OnLine (tuplePoint M (Local.decodeTuple r.2) i)
            (lineThrough r.1.1 p)) ∧
            ∀ i, tuplePoint M (Local.decodeTuple r.2) i ≠ p}).toReal *
          (K / Fintype.card F)
      else 0) ≤
      (4 * (4096 * 24 ^ 4) : ℝ) * K /
        (Fintype.card F : ℝ) ^ reuseSaving j := by
  let mass : Local.TupleCode F → Direction F → ℝ := fun c g =>
    (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
      (canonical_exposure_supported old a)).toOuterMeasure
      {M | (∀ i, OnLine (tuplePoint M (Local.decodeTuple c) i) (lineThrough g p)) ∧
        ∀ i, tuplePoint M (Local.decodeTuple c) i ≠ p}).toReal
  have heq :
      (∑ r : Slot F × Local.TupleCode F,
        if Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
            (oldGeneratorIndices (Local.decodeTuple r.2) old).card = j then
          mass r.2 r.1.1 * (K / Fintype.card F) else 0) =
      2 * ∑ c ∈ tupleCodesWithOldCount old j,
        globalTupleCodeTargetMass old a p c * (K / Fintype.card F) := by
    rw [sum_slot_tuple (fun c g =>
      if Function.Injective c.1 ∧ (∀ i, c.1 i ≠ g) ∧
          (oldGeneratorIndices (Local.decodeTuple c) old).card = j then
        mass c g * (K / Fintype.card F) else 0)]
    congr 1
    have hcodes : tupleCodesWithOldCount old j =
        Finset.univ.filter (fun c : Local.TupleCode F =>
          (oldGeneratorIndices (Local.decodeTuple c) old).card = j) := by
      ext c
      rw [Finset.mem_filter_univ]
      simp [tupleCodesWithOldCount, generatorLabelsWithOldCount,
        oldGeneratorIndices, Local.decodeTuple]
      rfl
    rw [hcodes, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hjc : (oldGeneratorIndices (Local.decodeTuple c) old).card = j
    · simp only [hjc, and_true, ite_true]
      by_cases hinj : Function.Injective c.1
      · simp only [hinj, true_and, globalTupleCodeTargetMass, ite_true,
          Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        by_cases hg : ∀ i, c.1 i ≠ g
        · rw [ite_eq_left hg, ite_eq_left hg]
          rfl
        · rw [ite_eq_right hg, ite_eq_right hg, zero_mul]
      · simp only [hinj, false_and, ite_false, globalTupleCodeTargetMass,
          zero_mul, Finset.sum_const_zero]
    · simp only [hjc, and_false, ite_false, Finset.sum_const_zero]
  exact heq.trans_le (sum_globalTupleCodeTargetMass_extension_le old a p j hold hj K hK)

end
end Balanced.ReuseConditional

end OAI
