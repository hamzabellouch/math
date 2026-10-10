import OAI.Probability.MatroidProphet.ProductRestriction
import OAI.Probability.MatroidProphet.AdaptiveResampling

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma bitsExpectation_comm (p : α → ℝ) (q : β → ℝ) (U : Finset α) (V : Finset β)
    (f : Finset α → Finset β → ℝ) :
    bitsExpectation p U (fun S => bitsExpectation q V (f S)) =
      bitsExpectation q V (fun T => bitsExpectation p U (fun S => f S T)) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_disjoint_union (q : α → ℝ) (U V : Finset α) (hUV : Disjoint U V)
    (f : Finset α → ℝ) :
    bitsExpectation q (U ∪ V) f =
      bitsExpectation q U (fun S => bitsExpectation q V (fun T => f (S ∪ T))) := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp only [empty_union, bitsExpectation_empty]
  | @insert e U he ih =>
    have heV : e ∉ V := fun hx => (Finset.disjoint_left.mp hUV (mem_insert_self e U) hx)
    have hU : Disjoint U V := hUV.mono_left (subset_insert e U)
    rw [insert_union, bitsExpectation_insert q (U ∪ V) e (by simp [he, heV]),
      bitsExpectation_insert q U e he, ih hU f, ih hU (fun S => f (insert e S))]
    simp only [insert_union]

lemma bitsExpectation_split (q : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → ℝ) :
    bitsExpectation q V f =
      bitsExpectation q (V \ U) (fun S => bitsExpectation q U (fun T => f (S ∪ T))) := by
  have heq : (V \ U) ∪ U = V := sdiff_union_of_subset hU
  rw [← bitsExpectation_disjoint_union q (V \ U) U sdiff_disjoint f, heq]

end MatroidProphet

end OAI
