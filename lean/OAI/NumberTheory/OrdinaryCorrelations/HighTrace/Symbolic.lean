import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Test
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeAt
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LinearCoeffZeroOfNot

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}
namespace PrivateFamily.Test
variable {w : ClosedLine h ℓ} (hl : ∀ i, w.label i ∈ D.members)
    {F : PrivateFamily w D L n} {j : Fin n}

noncomputable def symbolic : F.Test j → SquarefreeExpression S.Index ((ℓ+L)+L)
  | .extra | .tail _ =>
    ((SquarefreeExpression.zeroExpression S.Index ℓ).append
      ((F.witness j).spec.segmentExpression (F.witness j).spec.suffix.val (F.witness j).spec.length)).append
      (SquarefreeExpression.zeroExpression S.Index L)
  | .compare i _ r hi =>
    ((LineExpression.segment w hl (F.witness i).index (F.witness j).index).append
      ((F.witness j).spec.segmentExpression 0 (F.witness j).spec.tailStart.val)).append
      ((F.witness i).spec.segmentExpression 0 ((F.witness i).spec.activity r hi).val).neg

lemma symbolic_eval (t : F.Test j) :
    (t.symbolic hl).eval (fun p => ((p:ℕ):ℤ)) = t.expression := by
  cases t with
  | extra =>
    simp only [symbolic,SquarefreeExpression.eval_append,SquarefreeExpression.eval_zero,
      zero_add,add_zero,expression]
    exact (F.witness j).spec.segmentExpression_eval _ _ (Fin.isLt _).le le_rfl
  | tail q =>
    simp only [symbolic,SquarefreeExpression.eval_append,SquarefreeExpression.eval_zero,
      zero_add,add_zero,expression]
    exact (F.witness j).spec.segmentExpression_eval _ _ (Fin.isLt _).le le_rfl
  | compare i q r hi =>
    simp only [symbolic,SquarefreeExpression.eval_append,SquarefreeExpression.eval_neg,
      LineExpression.segment_eval]
    rw [(F.witness j).spec.segmentExpression_eval 0 _ (Nat.zero_le _) (Fin.isLt _).le,
      (F.witness i).spec.segmentExpression_eval 0 _ (Nat.zero_le _)
        (Nat.lt_succ_iff.mp ((F.witness i).spec.activity r hi).isLt)]
    change w.offset (F.witness j).index-w.offset (F.witness i).index+
      ((F.witness j).spec.offset (F.witness j).spec.tailStart.castSucc-(F.witness j).spec.offset 0)+
      -((F.witness i).spec.offset ((F.witness i).spec.activity r hi)-(F.witness i).spec.offset 0) = _
    rw [(F.witness j).spec.offset_zero,(F.witness i).spec.offset_zero]
    simp only [expression,AttachedSpec.vertex,sub_eq_add_neg,neg_zero,add_zero]

lemma symbolic_coefficient (t : F.Test j) :
    (t.symbolic hl).linearCoeff t.selected (fun p => ((p:ℕ):ℤ)) = t.coefficient := by
  cases t with
  | extra =>
    simp only [symbolic,selected,SquarefreeExpression.coefficient_append,
      SquarefreeExpression.coefficient_zero,zero_add,add_zero,coefficient]
    exact SquarefreeExpression.linearCoeff_zero_of_not_support _ _
      ((F.witness j).spec.segmentExpression_extra_absent _ _) _
  | tail q =>
    simp only [symbolic,selected,SquarefreeExpression.coefficient_append,
      SquarefreeExpression.coefficient_zero,zero_add,add_zero,coefficient]
    exact (F.witness j).spec.segmentExpression_coefficient _ _ le_rfl _
  | compare i q r hi =>
    simp only [symbolic,selected,SquarefreeExpression.coefficient_append,
      SquarefreeExpression.coefficient_neg,LineExpression.segment_coefficient]
    rw [(F.witness j).spec.segmentExpression_coefficient 0 _ (Fin.isLt _).le,
      (F.witness i).spec.segmentExpression_coefficient 0 _
        (Nat.lt_succ_iff.mp ((F.witness i).spec.activity r hi).isLt)]
    rfl

lemma symbolic_support (t : F.Test j) {p : S.Index}
    (hp : p ∈ (t.symbolic hl).support) : (p:ℕ) ∈ t.support := by
  cases t with
  | extra =>
    simp only [symbolic,SquarefreeExpression.support_append,SquarefreeExpression.support_zero,
      empty_union,union_empty] at hp
    exact (F.witness j).spec.segmentExpression_support _ _ hp
  | tail q =>
    simp only [symbolic,SquarefreeExpression.support_append,SquarefreeExpression.support_zero,
      empty_union,union_empty] at hp
    exact (F.witness j).spec.segmentExpression_support _ _ hp
  | compare i q r hi =>
    simp only [symbolic,SquarefreeExpression.support_append,SquarefreeExpression.support_neg,mem_union] at hp
    rcases hp with (hp|hp)|hp
    · exact mem_union_right _ (LineExpression.segment_support w hl _ _ hp)
    · exact mem_union_left _ (mem_union_right _ ((F.witness j).spec.segmentExpression_support _ _ hp))
    · exact mem_union_left _ (mem_union_left _ ((F.witness i).spec.segmentExpression_support _ _ hp))

lemma symbolic_own_absent (t : F.Test j) (ht : ¬t.Linear) : t.selected ∉ (t.symbolic hl).support := by
  cases t with
  | extra =>
    simp only [symbolic,selected,SquarefreeExpression.support_append,SquarefreeExpression.support_zero,
      empty_union,union_empty]
    exact (F.witness j).spec.segmentExpression_extra_absent _ _
  | tail q => exact (ht trivial).elim
  | compare i q r hi => exact (ht trivial).elim

lemma symbolic_factor_card (t : F.Test j) (i : Fin ((ℓ+L)+L)) :
    ((t.symbolic hl).factors i).card ≤ ⌈C₀*Real.log B⌉₊ := by
  cases t with
  | extra | tail =>
    apply SquarefreeExpression.factors_append_le _ _ _ _ _ i
    · apply SquarefreeExpression.factors_append_le
      · intro e; simp [SquarefreeExpression.zeroExpression]
      · exact fun e => (F.witness j).spec.segmentExpression_factor_card _ _ e
    · intro e; simp [SquarefreeExpression.zeroExpression]
  | compare a q r ha =>
    apply SquarefreeExpression.factors_append_le _ _ _ _ _ i
    · apply SquarefreeExpression.factors_append_le
      · exact fun e => LineExpression.segment_factor_card w hl _ _ e
      · exact fun e => (F.witness j).spec.segmentExpression_factor_card _ _ e
    · exact fun e => (F.witness a).spec.segmentExpression_factor_card 0 ((F.witness a).spec.activity r ha).val e

lemma symbolic_coeff_bound (t : F.Test j) (i : Fin ((ℓ+L)+L)) :
    |((t.symbolic hl).coefficient i:ℝ)| ≤ (h:ℝ) := by
  cases t with
  | extra | tail =>
    apply SquarefreeExpression.abs_coefficient_append_le _ _ _ _ _ i
    · apply SquarefreeExpression.abs_coefficient_append_le
      · intro e; simp [SquarefreeExpression.zeroExpression]
      · exact fun e => (F.witness j).spec.segmentExpression_coeff_bound _ _ e
    · intro e; simp [SquarefreeExpression.zeroExpression]
  | compare a q r ha =>
    apply SquarefreeExpression.abs_coefficient_append_le _ _ _ _ _ i
    · apply SquarefreeExpression.abs_coefficient_append_le
      · exact fun e => LineExpression.segment_coeff_bound w hl _ _ e
      · exact fun e => (F.witness j).spec.segmentExpression_coeff_bound _ _ e
    · intro e
      simpa only [SquarefreeExpression.neg,Int.cast_neg,abs_neg] using
        (F.witness a).spec.segmentExpression_coeff_bound 0 ((F.witness a).spec.activity r ha).val e

lemma symbolic_size (t : F.Test j) (hB : 0 ≤ B) (x : S.Index → ℕ)
    (hx : ∀ p, (x p:ℝ) ≤ Real.exp B) :
    |((t.symbolic hl).eval (fun p => (x p:ℤ)):ℝ)| ≤
      ((ℓ+L)+L)*h*Real.exp (B*⌈C₀*Real.log B⌉₊) := by
  have hb := SquarefreeExpression.abs_eval_le (t.symbolic hl) ⌈C₀*Real.log B⌉₊ B (h:ℝ)
    hB (Nat.cast_nonneg h) (t.symbolic_factor_card hl) (t.symbolic_coeff_bound hl)
    (fun p => (x p:ℤ)) (by
      intro p hp
      simpa only [Int.cast_natCast,abs_of_nonneg (show (0:ℝ) ≤ (x p:ℝ) from Nat.cast_nonneg _)] using hx p)
  simpa only [Nat.cast_add] using hb

end PrivateFamily.Test
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
