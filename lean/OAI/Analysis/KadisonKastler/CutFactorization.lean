import OAI.Analysis.KadisonKastler.TupleSplitting
import OAI.Analysis.KadisonKastler.OrderedCutMatrices
import OAI.Analysis.KadisonKastler.HilbertColumns

namespace OAI

/-!
# Exact matrix factorizations of ordered cut sums

These identities turn the combinatorial splitting of a word into a
row-matrix-column product. The identities apply to arbitrary prefix and suffix operators.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cutFactorizationOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance cutFactorizationStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
/-- Expand the single entry of an operator row-matrix-column product. -/
theorem operator_sandwich_entry {I J : Type*} [Fintype I] [Fintype J]
    (L : I → H →L[ℂ] H) (T : CStarMatrix I J (H →L[ℂ] H))
    (R : J → H →L[ℂ] H) :
    (operatorRow L * T * operatorColumn R) () () =
      ∑ i, ∑ j, L i * T i j * R j := by
  simp only [CStarMatrix.mul_apply, operatorRow_apply, operatorColumn_apply, sum_mul]
  rw [sum_comm]

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [CompleteSpace H] in
/-- Prefixes have length `p` and suffixes length `q`; the adjacency matrix takes column length first, hence its parameters are `q p`. -/
theorem noPreservation_sum_eq_sandwich (W : Finset α) (p q : ℕ)
    (L : OrderedLabelTuple W p → H →L[ℂ] H)
    (R : OrderedLabelTuple W q → H →L[ℂ] H) :
    (∑ t : OrderedLabelTuple W (p + q), L (tupleInitial t) * R (tupleFinal t)) =
      (operatorRow L * orderedNoPreservationMatrix (H := H) W q p * operatorColumn R) () () := by
  have hsum : (∑ t : OrderedLabelTuple W (p + q), L (tupleInitial t) * R (tupleFinal t)) =
      ∑ a, ∑ b, if Disjoint (tupleSubset a).val (tupleSubset b).val then L a * R b else 0 := by
    rw [sum_orderedTuple_split W p q]
    simp only [tupleInitial_join, tupleFinal_join]
    exact sum_disjointOrderedTuplePair W p q (fun a b => L a * R b)
  rw [hsum, operator_sandwich_entry]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [orderedNoPreservationMatrix_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]

/-- The operator at the uniquely omitted label, with zero on intersecting pairs. -/
def orderedMissingLabelMatrix (W : Finset α) {p q : ℕ} (hW : W.card = p + 1 + q)
    (D : α → H →L[ℂ] H) :
    CStarMatrix (OrderedLabelTuple W p) (OrderedLabelTuple W q) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun a b => if h : Disjoint (tupleSubset a).val (tupleSubset b).val
    then D (tuplePairMissing hW ⟨(a, b), h⟩) else 0

omit [Fintype α] [CompleteSpace H] in
@[simp]
theorem orderedMissingLabelMatrix_apply (W : Finset α) {p q : ℕ}
    (hW : W.card = p + 1 + q) (D : α → H →L[ℂ] H)
    (a : OrderedLabelTuple W p) (b : OrderedLabelTuple W q) :
    orderedMissingLabelMatrix W hW D a b =
      if h : Disjoint (tupleSubset a).val (tupleSubset b).val
      then D (tuplePairMissing hW ⟨(a, b), h⟩) else 0 := rfl

private theorem sum_subtype_extension {I B : Type*} [Fintype I] [AddCommMonoid B]
    (P : I → Prop) [DecidablePred P] (f : {i // P i} → B) :
    (∑ i, f i) = ∑ i, if h : P i then f ⟨i, h⟩ else 0 := by
  classical
  let F : I → B := fun i => if h : P i then f ⟨i, h⟩ else 0
  have hf : (∑ i, f i) = ∑ i : {i // P i}, F i.val := by
    apply sum_congr rfl
    intro i _
    simp only [F, dite_eq_left i.property]
  rw [hf, ← Finset.sum_subtype (univ.filter P) (by simp) F, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : P i <;> simp only [F, hi, ite_true, ite_false, dite_true, dite_false]

omit [CompleteSpace H] in
/-- The exact preservation-cut factorization, before any norm estimate. -/
theorem preservation_sum_eq_sandwich (W : Finset α) (p q : ℕ)
    (hW : W.card = p + 1 + q)
    (L : OrderedLabelTuple W p → H →L[ℂ] H) (D : α → H →L[ℂ] H)
    (R : OrderedLabelTuple W q → H →L[ℂ] H) :
    (∑ t : OrderedLabelTuple W (p + 1 + q),
      L (tupleDropMiddle t).val.1 * D (tupleMiddle t) * R (tupleDropMiddle t).val.2) =
      (operatorRow L * orderedMissingLabelMatrix W hW D * operatorColumn R) () () := by
  rw [sum_orderedTuple_middle W p q hW]
  simp only [tupleDropMiddle_insertMiddle, tupleMiddle_insertMiddle]
  rw [sum_subtype_extension
    (fun ab : OrderedLabelTuple W p × OrderedLabelTuple W q =>
      Disjoint (tupleSubset ab.1).val (tupleSubset ab.2).val),
    Fintype.sum_prod_type, operator_sandwich_entry]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [orderedMissingLabelMatrix_apply]
  split_ifs <;> simp

/-- The two diagonal compressions act entry by entry. -/
theorem preservationSubsetMatrix_apply (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H) (P : H →L[ℂ] H) (d : ℝ)
    (a : WordSubset W q) (b : WordSubset W p) :
    preservationSubsetMatrix W hW e P d a b =
      P * ((if h : Disjoint a.val b.val then e (missingWordLabel W hW a b h) else 0) -
        (d⁻¹ : ℂ) • (if Disjoint a.val b.val then 1 else 0)) * P := by
  change (Matrix.diagonal (fun _ : WordSubset W q => P) *
    Matrix.of (fun (a : WordSubset W q) (b : WordSubset W p) =>
      (if h : Disjoint a.val b.val then e (missingWordLabel W hW a b h) else 0) -
      (d⁻¹ : ℂ) • (if Disjoint a.val b.val then 1 else 0)) *
    Matrix.diagonal (fun _ : WordSubset W p => P)) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- The missing-label matrix equals the compressed preservation matrix.
The identity itself holds for every compression operator. -/
theorem orderedMissingLabelMatrix_eq_preservation (W : Finset α) {p q : ℕ}
    (hW : W.card = p + 1 + q) (e : α → H →L[ℂ] H) (P : H →L[ℂ] H) (d : ℝ) :
    orderedMissingLabelMatrix W hW (fun a => P * (e a - (d⁻¹ : ℂ) • 1) * P) =
      orderedPreservationMatrix W (p := q) (q := p) (by omega) e P d := by
  apply CStarMatrix.ext
  intro a b
  rw [orderedMissingLabelMatrix_apply]
  change _ = preservationSubsetMatrix W _ e P d (tupleSubset a) (tupleSubset b)
  rw [preservationSubsetMatrix_apply]
  split_ifs with h
  · rfl
  · simp

end

end KadisonKastler

end OAI
