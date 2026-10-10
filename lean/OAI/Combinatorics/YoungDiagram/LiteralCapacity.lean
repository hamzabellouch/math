import OAI.Combinatorics.YoungDiagram.LargeCapacity
import OAI.RepresentationTheory.TensorSquares.Arithmetic

namespace OAI

/- Literal integer-floor capacities and the parity-compatible triangular parameters. -/
namespace ArithmeticTensorSquares.Capacity
open scoped BigOperators

/-- Integer Euclidean division by positive2 is the literal integer floor.
Unlike Nat subtraction, this expression retains negative h-d before clamping. -/
def literalAttachmentCapacity (height : Nat → Nat) (d q : Nat) : Int :=
  ∑ i ∈ Finset.range q, max 0 (((height i : Int)-(d : Int))/2)

def LiteralBandTest (height width : Nat → Nat) (M r : Nat) : Prop :=
  ∃ d q : Nat, 1 ≤ d ∧ d ≤ 4 ∧ q ≤ 8 ∧
    2*M-1 ≤ ∑ i ∈ Finset.range d, width i ∧
    d*q+7+d ≤ 2*M-1 ∧ (r : Int) ≤ literalAttachmentCapacity height d q

lemma attachment_term_eq (h d : Nat) :
    max 0 (((h : Int)-(d : Int))/2) = (((h-d)/2 : Nat) : Int) := by
  omega

lemma literalAttachmentCapacity_eq (height : Nat → Nat) (d q : Nat) :
    literalAttachmentCapacity height d q = (attachmentCapacity height d q : Int) := by
  have cast_sum (s : Finset Nat) :
      (∑ i ∈ s, (((height i-d)/2 : Nat) : Int)) =
        ((∑ i ∈ s, (height i-d)/2 : Nat) : Int) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Nat.cast_zero]
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Nat.cast_add, ih]
  simp only [literalAttachmentCapacity, attachmentCapacity, attachment_term_eq]
  exact cast_sum (Finset.range q)

lemma bandTest_literal_iff (height width : Nat → Nat) (M r : Nat) :
    BandTest height width M r ↔ LiteralBandTest height width M r := by
  simp [BandTest, LiteralBandTest, literalAttachmentCapacity_eq]

lemma twice_triangular (m : Nat) :
    2*UniversalTensorSquares.triangular m = m*(m+1) := by
  induction m with
  | zero => simp [UniversalTensorSquares.triangular]
  | succ m ih =>
    rw [UniversalTensorSquares.triangular_succ]
    nlinarith

/-- The literal band criterion for the parity-compatible triangular index and remainder,
with both first-four prefix bounds. -/
theorem capacity_large (n : Nat) (μ : YoungDiagram) (hcard : μ.card = n)
    (hM : 22 ≤ UniversalTensorSquares.largestIndex n)
    (hr : 0 < UniversalTensorSquares.remainderPairs n)
    (hcols : 2*UniversalTensorSquares.largestIndex n-1 ≤ colPrefix μ 4)
    (hrows : 2*UniversalTensorSquares.largestIndex n-1 ≤ rowPrefix μ 4) :
    LiteralBandTest μ.colLen μ.rowLen
      (UniversalTensorSquares.largestIndex n) (UniversalTensorSquares.remainderPairs n) ∨
    LiteralBandTest μ.rowLen μ.colLen
      (UniversalTensorSquares.largestIndex n) (UniversalTensorSquares.remainderPairs n) := by
  have hsize : 2*μ.card = UniversalTensorSquares.largestIndex n *
      (UniversalTensorSquares.largestIndex n+1)+4*UniversalTensorSquares.remainderPairs n := by
    have hd := UniversalTensorSquares.degree_decomposition n
    have ht := twice_triangular (UniversalTensorSquares.largestIndex n)
    rw [hcard]
    nlinarith
  have hrange : 2*UniversalTensorSquares.remainderPairs n ≤
      3*UniversalTensorSquares.largestIndex n+4 := by
    rcases Nat.mod_two_eq_zero_or_one (UniversalTensorSquares.largestIndex n) with he | ho
    · exact UniversalTensorSquares.even_index_remainder_bound n he
    · have h := UniversalTensorSquares.odd_index_remainder_bound n ho
      omega
  rcases capacity_large_numeric μ _ _ hM hr hsize hrange hcols hrows with h | h
  · exact Or.inl ((bandTest_literal_iff _ _ _ _).mp h)
  · exact Or.inr ((bandTest_literal_iff _ _ _ _).mp h)

end ArithmeticTensorSquares.Capacity

end OAI
