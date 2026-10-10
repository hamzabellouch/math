import OAI.Combinatorics.ContingencyTables.Transport.IntegerTruncatedTransport

namespace OAI

/-! # The auxiliary kernel enumerates exactly one excess ordinary pair

The finite assignment carries its excess-pair position. Its raw full
profile recovers the position and every choice uniquely. Box truncation
removes exactly the two inadmissible endpoints of that excess pair.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal BalancedBox
open IntegerBoxTruncation

/-- One distinguished ordinary pair has occupancy U+1. -/
@[reducible] def ExcessAssignments : List ℕ → Type
  | [] => Empty
  | U::Ms => (Assignments Ms × Fin (U+2)) ⊕ (ExcessAssignments Ms × Fin (U+1))

@[reducible] instance excessAssignmentsFintype (Ms : List ℕ) : Fintype (ExcessAssignments Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons U Ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Assignments Ms × Fin (U+2)) ⊕
      (ExcessAssignments Ms × Fin (U+1))))

def excessEmbedding {I : Type*} : (Ms : List ℕ) → (I → ℕ) →
    ExcessAssignments Ms → Coordinates I Ms → ℕ
  | [],_,a => Empty.elim a
  | U::Ms,z,.inl a => profile (embedding Ms z a.1) a.2.val (U+1-a.2.val)
  | U::Ms,z,.inr a => profile (excessEmbedding Ms z a.1) a.2.val (U-a.2.val)

def ValidExcess : (Ms : List ℕ) → ExcessAssignments Ms → Prop
  | [],a => Empty.elim a
  | U::_,.inl a => 0 < a.2.val ∧ a.2.val ≤ U
  | _::Ms,.inr a => ValidExcess Ms a.1

/-- Exact finite expansion of the actual recursive auxiliary kernel. -/
theorem auxiliaryKernel_eq_excess_sum {I : Type*} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    auxiliaryKernel Ms F z=∑ a : ExcessAssignments Ms, F (excessEmbedding Ms z a) := by
  induction Ms with
  | nil => simp only [auxiliaryKernel,ExcessAssignments,Finset.univ_eq_empty,Finset.sum_empty]
  | cons U Ms ih =>
    change marginal (exposedFamily Ms F) (U+1) z+auxiliaryKernel Ms (marginal F U) z=
      ∑ a : (Assignments Ms × Fin (U+2)) ⊕ (ExcessAssignments Ms × Fin (U+1)),
        F (excessEmbedding (U::Ms) z a)
    rw [Fintype.sum_sum_type]
    congr 1
    · unfold marginal exposedFamily
      simp_rw [eliminate_eq_sum,expose_embedding]
      rw [Finset.sum_comm,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      exact (Fin.sum_univ_eq_sum_range
        (fun j => F (profile (embedding Ms z a) j (U+1-j))) (U+2)).symm
    · rw [ih,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      unfold marginal
      exact (Fin.sum_univ_eq_sum_range
        (fun j => F (profile (excessEmbedding Ms z a) j (U-j))) (U+1)).symm

lemma excessEmbedding_injective {I : Type*} (Ms : List ℕ) (z : I → ℕ) :
    Function.Injective (excessEmbedding Ms z) := by
  induction Ms with
  | nil => intro a; exact Empty.elim a
  | cons U Ms ih =>
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hj := congrFun he (.inr false)
        change a.2.val=b.2.val at hj
        have ho : embedding Ms z a.1=embedding Ms z b.1 := by
          funext i
          exact congrFun he (.inl i)
        exact congrArg Sum.inl (Prod.ext (embedding_injective Ms z ho) (Fin.ext hj))
      | inr b =>
        have hj := congrFun he (.inr false)
        have hk := congrFun he (.inr true)
        change a.2.val=b.2.val at hj
        change U+1-a.2.val=U-b.2.val at hk
        have ha := a.2.isLt
        have hb := b.2.isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hj := congrFun he (.inr false)
        have hk := congrFun he (.inr true)
        change a.2.val=b.2.val at hj
        change U-a.2.val=U+1-b.2.val at hk
        have ha := a.2.isLt
        have hb := b.2.isLt
        omega
      | inr b =>
        have hj := congrFun he (.inr false)
        change a.2.val=b.2.val at hj
        have ho : excessEmbedding Ms z a.1=excessEmbedding Ms z b.1 := by
          funext i
          exact congrFun he (.inl i)
        exact congrArg Sum.inr (Prod.ext (ih ho) (Fin.ext hj))

lemma excessEmbedding_total {I : Type*} [Fintype I] (Ms : List ℕ)
    (z : I → ℕ) (a : ExcessAssignments Ms) :
    (∑ i, excessEmbedding Ms z a i)=(∑ i, z i)+Ms.sum+1 := by
  induction Ms with
  | nil => exact Empty.elim a
  | cons U Ms ih =>
    cases a with
    | inl a =>
      change (∑ i, profile (embedding Ms z a.1) a.2.val (U+1-a.2.val) i)=_
      rw [profile_total,embedding_total]
      have ha := a.2.isLt
      simp only [List.sum_cons]
      omega
    | inr a =>
      change (∑ i, profile (excessEmbedding Ms z a.1) a.2.val (U-a.2.val) i)=_
      rw [profile_total,ih]
      have ha := a.2.isLt
      simp only [List.sum_cons]
      omega

lemma excessEmbedding_inBox_iff {I : Type*} (Ms : List ℕ) (m z : I → ℕ)
    (hz : InBox m z) (a : ExcessAssignments Ms) :
    InBox (bounds m Ms) (excessEmbedding Ms z a) ↔ ValidExcess Ms a := by
  induction Ms with
  | nil => exact Empty.elim a
  | cons U Ms ih =>
    cases a with
    | inl a =>
      constructor
      · intro h
        have ha := h (.inr false)
        have hb := h (.inr true)
        change a.2.val ≤ U at ha
        change U+1-a.2.val ≤ U at hb
        change 0 < a.2.val ∧ a.2.val ≤ U
        omega
      · intro h
        apply profile_inBox (bounds m Ms) (embedding Ms z a.1) U a.2.val (U+1-a.2.val)
        · exact embedding_inBox Ms m z hz a.1
        · exact h.2
        · have ha := h.1
          omega
    | inr a =>
      constructor
      · intro h
        apply (ih a.1).mp
        intro i
        exact h (.inl i)
      · intro h
        apply profile_inBox (bounds m Ms) (excessEmbedding Ms z a.1) U a.2.val (U-a.2.val)
        · exact (ih a.1).mpr h
        · have ha := a.2.isLt
          omega
        · exact Nat.sub_le _ _

/-- The zero-extended auxiliary count includes precisely the admissible
single-excess-pair profiles, each once. -/
theorem auxiliaryKernel_truncate_eq_valid_sum {I : Type*} [Fintype I]
    (Ms : List ℕ) (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)+1=R) :
    auxiliaryKernel Ms (truncate F (bounds m Ms) (R+Ms.sum)) z=
      ∑ a ∈ Finset.univ.filter (ValidExcess Ms), F (excessEmbedding Ms z a) := by
  rw [auxiliaryKernel_eq_excess_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have ht : (∑ i, excessEmbedding Ms z a i)=R+Ms.sum := by
    rw [excessEmbedding_total]
    omega
  simp only [truncate,ht,excessEmbedding_inBox_iff Ms m z hz a,and_true]

end ContingencyTables.IntegerWeightedTransport

end OAI
