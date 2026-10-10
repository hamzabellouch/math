import OAI.Probability.MatroidProphet.Residual.Probability

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_union (p q : α → ℝ) (V : Finset α) (f : Finset α → ℝ) :
    bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (D ∪ C))) =
      bitsExpectation (fun e => p e + (1 - p e) * q e) V f := by
  induction V using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert p V e he,
      bitsExpectation_insert (fun e => p e + (1 - p e) * q e) V e he]
    have hno : bitsExpectation p V (fun D => bitsExpectation q (insert e V) (fun C => f (D ∪ C))) =
        (1 - q e) * bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (D ∪ C))) +
        q e * bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (insert e (D ∪ C)))) := by
      simp_rw [bitsExpectation_insert q V e he, union_insert]
      rw [bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_mul_const]
    have hyes : bitsExpectation p V (fun D => bitsExpectation q (insert e V) (fun C => f (insert e D ∪ C))) =
        bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (insert e (D ∪ C)))) := by
      apply bitsExpectation_congr
      intro D hD
      rw [bitsExpectation_insert q V e he]
      simp only [insert_union, union_insert, insert_idem]
      ring
    rw [hno, hyes, ih f, ih (fun S => f (insert e S))]
    ring

end MatroidProphet

end OAI
