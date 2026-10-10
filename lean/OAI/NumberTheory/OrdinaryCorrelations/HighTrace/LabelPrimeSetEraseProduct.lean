import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LabelPrimeSet
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.HarmonicCongruenceBound
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SquarefreeExpression
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexAt

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

lemma labelPrimeSet_erase_product (d : ℕ) (hd : d ∈ D.members) (q : S.Index)
    (hq : q ∈ labelPrimeSet d hd) :
    (∏ p ∈ (labelPrimeSet d hd).erase q, p.val) = d/q.val := by
  have he := (mul_prod_erase (labelPrimeSet d hd) (fun p => p.val) hq).trans
    (labelPrimeSet_product d hd)
  calc
    _ = ((q:ℕ)*(∏ p ∈ (labelPrimeSet d hd).erase q, p.val))/(q:ℕ) :=
      (Nat.mul_div_cancel_left _ (S.prime_mem q q.property).pos).symm
    _ = _ := congrArg (fun n : ℕ => n/(q:ℕ)) he

namespace Specification
variable (s : S.Specification D h L)

noncomputable def segmentExpression (a b : ℕ) : SquarefreeExpression S.Index L where
  factors i := if hi : i.val<s.length then labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _) else ∅
  coefficient i := if hi : i.val<s.length then
    if a ≤ i.val ∧ i.val<b then s.sign ⟨i.val,hi⟩*(h:ℤ) else 0
    else 0

lemma segmentExpression_factor_card (a b : ℕ) (i : Fin L) :
    ((s.segmentExpression a b).factors i).card ≤ ⌈C₀*Real.log B⌉₊ := by
  unfold segmentExpression
  dsimp only
  split_ifs
  · rw [labelPrimeSet_card]; exact D.omega _ (s.label_mem _)
  · simp

lemma segmentExpression_support (a b : ℕ) {p : S.Index}
    (hp : p ∈ (s.segmentExpression a b).support) : p.val ∈ s.primeSupport := by
  obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
  split_ifs at hp with hc
  · simp at hp
  · change p ∈ (if hi : i.val<s.length then labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _) else ∅) at hp
    split_ifs at hp with hi
    · exact mem_insert_of_mem (mem_biUnion.mpr
        ⟨⟨i.val,hi⟩,mem_univ _,(mem_labelPrimeSet _ _ p).mp hp⟩)
    · simp at hp

lemma segmentExpression_extra_absent (a b : ℕ) : s.extra ∉ (s.segmentExpression a b).support := by
  intro hp
  obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
  split_ifs at hp with hc
  · simp at hp
  · change s.extra ∈ (if hi : i.val<s.length then labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _) else ∅) at hp
    split_ifs at hp with hi
    · exact s.extra_not_div _ ((Nat.mem_primeFactors.mp ((mem_labelPrimeSet _ _ _).mp hp)).2.1)
    · simp at hp

lemma segmentExpression_eval_term (a b : ℕ) (i : Fin L) :
    (s.segmentExpression a b).coefficient i *
      ∏ p ∈ (s.segmentExpression a b).factors i, ((p:ℕ):ℤ) =
    if a ≤ i.val ∧ i.val<b then s.edgeAt i.val else 0 := by
  by_cases hi : i.val<s.length
  · have hp : (∏ p ∈ labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _), ((p:ℕ):ℤ)) =
        (s.label ⟨i.val,hi⟩:ℤ) := by
      exact_mod_cast labelPrimeSet_product (s.label ⟨i.val,hi⟩) (s.label_mem _)
    simp only [segmentExpression,dite_eq_left hi,edgeAt,hp]
    split_ifs <;> simp
  · simp [segmentExpression,hi,edgeAt]

lemma range_filter_interval (a b : ℕ) (hb : b ≤ L) :
    (range L).filter (fun n => a ≤ n ∧ n<b) = Ico a b := by
  ext n
  simp only [mem_filter,mem_range,mem_Ico]
  omega

lemma segmentExpression_eval (a b : ℕ) (hab : a ≤ b) (hb : b ≤ s.length) :
    (s.segmentExpression a b).eval (fun p => ((p:ℕ):ℤ)) =
      s.offset ⟨b,by omega⟩-s.offset ⟨a,by omega⟩ := by
  unfold SquarefreeExpression.eval
  simp_rw [segmentExpression_eval_term]
  rw [Fin.sum_univ_eq_sum_range (fun n => if a ≤ n ∧ n<b then s.edgeAt n else 0) L,
    ←sum_filter,range_filter_interval a b (hb.trans s.length_le)]
  exact (s.displacement_eq_sum a b hab hb).symm

lemma segmentExpression_coefficient_term (a b : ℕ) (q : S.Index) (i : Fin L) :
    (if q ∈ (s.segmentExpression a b).factors i then
      (s.segmentExpression a b).coefficient i *
        ∏ p ∈ ((s.segmentExpression a b).factors i).erase q, ((p:ℕ):ℤ) else 0) =
      if a ≤ i.val ∧ i.val<b then s.coefficientAt q i.val else 0 := by
  by_cases hi : i.val<s.length
  · have hq : q ∈ labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _) ↔
        (q:ℕ) ∣ s.label ⟨i.val,hi⟩ := by
      rw [mem_labelPrimeSet]
      exact ⟨fun hp => (Nat.mem_primeFactors.mp hp).2.1,fun hp =>
        Nat.mem_primeFactors.mpr ⟨S.prime_mem q q.property,hp,
          (lt_trans Nat.zero_lt_one (D.greater_one _ (s.label_mem _))).ne'⟩⟩
    simp only [segmentExpression,dite_eq_left hi,coefficientAt]
    by_cases hmem : q ∈ labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _)
    · have hp : (∏ p ∈ (labelPrimeSet (s.label ⟨i.val,hi⟩) (s.label_mem _)).erase q, ((p:ℕ):ℤ)) =
          ((s.label ⟨i.val,hi⟩/(q:ℕ):ℕ):ℤ) := by
        exact_mod_cast labelPrimeSet_erase_product _ (s.label_mem _) q hmem
      simp only [hmem,ite_true,hp,ite_eq_left (hq.mp hmem)]
      split_ifs <;> simp
    · simp only [hmem,ite_false,ite_eq_right (mt hq.mpr hmem)]
      split_ifs <;> rfl
  · simp [segmentExpression,hi,coefficientAt]

lemma segmentExpression_coefficient (a b : ℕ) (hb : b ≤ s.length) (q : S.Index) :
    (s.segmentExpression a b).linearCoeff q (fun p => ((p:ℕ):ℤ)) =
      s.coefficient q a b := by
  unfold SquarefreeExpression.linearCoeff
  simp_rw [segmentExpression_coefficient_term]
  rw [Fin.sum_univ_eq_sum_range (fun n => if a ≤ n ∧ n<b then s.coefficientAt q n else 0) L,
    ←sum_filter,range_filter_interval a b (hb.trans s.length_le)]
  rfl

lemma segmentExpression_coeff_bound (a b : ℕ) (i : Fin L) :
    |((s.segmentExpression a b).coefficient i:ℝ)| ≤ (h:ℝ) := by
  unfold segmentExpression
  dsimp only
  split_ifs with hi hab
  · obtain hs | hs := s.sign_mem ⟨i.val,hi⟩ <;> simp [hs]
  · simp
  · simp

end Specification
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
