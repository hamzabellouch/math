import OAI.Analysis.KadisonKastler.OrderedTuples
import OAI.Analysis.KadisonKastler.TupleMatrices

namespace OAI

/-!
# Ordered matrices at free-word cuts

Subset cut matrices are lifted along the map forgetting the order of a
tuple. The exact factorial fibre sizes give the required square-root
factorial costs. Complementary-subset adjacency is contractive.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance orderedCutOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance orderedCutOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The preservation matrix with ordered row and column labels. -/
def orderedPreservationMatrix (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H) (P : H →L[ℂ] H) (d : ℝ) :
    CStarMatrix (OrderedLabelTuple W q) (OrderedLabelTuple W p) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun A B =>
    preservationSubsetMatrix W hW e P d (tupleSubset A) (tupleSubset B)

/-- Replication costs the square roots of the exact ordering multiplicities. -/
theorem norm_orderedPreservationMatrix_le (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H)
    (he : ∀ a, IsStarProjection (e a)) (horth : ∀ a b, a ≠ b → e a * e b = 0)
    (P : H →L[ℂ] H) (hP : IsStarProjection P) {d : ℝ} (hd : 0 < d) :
    ‖orderedPreservationMatrix W hW e P d‖ ≤
      Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ) *
        (1 + Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) / d) := by
  have hrep := norm_replicatedMatrix_le (H := H)
    (tupleSubset (W := W) (p := q)) (tupleSubset (W := W) (p := p))
    q.factorial p.factorial
    (fun B => (card_filter_tupleSubset B).le) (fun B => (card_filter_tupleSubset B).le)
    (preservationSubsetMatrix W hW e P d)
  calc
    _ ≤ Real.sqrt (q.factorial : ℝ) * ‖preservationSubsetMatrix W hW e P d‖ *
        Real.sqrt (p.factorial : ℝ) := hrep
    _ ≤ Real.sqrt (q.factorial : ℝ) *
        (1 + Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) / d) *
        Real.sqrt (p.factorial : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (norm_preservationSubsetMatrix_le W hW e he horth P hP hd) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A subset of size `q` has exactly one disjoint complementary subset of
size `p` when the ambient label set has size `p + q`. -/
theorem card_complementary_wordSubsets (W : Finset α) (p q : ℕ)
    (hW : W.card = p + q) (A : WordSubset W q) :
    #{B : WordSubset W p | Disjoint A.val B.val} = 1 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (disjointWordSubsetEquiv W A.val p),
    card_wordSubset, card_sdiff_of_subset A.property.1, A.property.2, hW,
    Nat.add_sub_cancel_right, Nat.choose_self]

/-- The subset adjacency occurring at a cut with no preservation letter. -/
def noPreservationSubsetMatrix (W : Finset α) (p q : ℕ) :
    CStarMatrix (WordSubset W q) (WordSubset W p) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun A B => if Disjoint A.val B.val then 1 else 0

theorem norm_noPreservationSubsetMatrix_le (W : Finset α) (p q : ℕ)
    (hW : W.card = p + q) : ‖noPreservationSubsetMatrix (H := H) W p q‖ ≤ 1 := by
  classical
  have h := norm_matrix_le_sqrt_degrees (noPreservationSubsetMatrix (H := H) W p q)
    (fun A B => Disjoint A.val B.val) 1 1
  simp only [Nat.cast_one, one_mul, Real.sqrt_one] at h
  apply h
  · intro A B hAB
    change (if Disjoint A.val B.val then (1 : H →L[ℂ] H) else 0) = 0
    simp [hAB]
  · intro A B
    change ‖if Disjoint A.val B.val then (1 : H →L[ℂ] H) else 0‖ ≤ 1
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp
  · intro A
    exact (card_complementary_wordSubsets W p q hW A).le
  · intro B
    have hb := card_complementary_wordSubsets W q p (by omega) B
    simpa only [disjoint_comm] using hb.le

def orderedNoPreservationMatrix (W : Finset α) (p q : ℕ) :
    CStarMatrix (OrderedLabelTuple W q) (OrderedLabelTuple W p) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun A B =>
    noPreservationSubsetMatrix W p q (tupleSubset A) (tupleSubset B)

omit [Fintype α] [CompleteSpace H] in
@[simp]
theorem orderedNoPreservationMatrix_apply (W : Finset α) (p q : ℕ)
    (A : OrderedLabelTuple W q) (B : OrderedLabelTuple W p) :
    orderedNoPreservationMatrix (H := H) W p q A B =
      if Disjoint (tupleSubset A).val (tupleSubset B).val then 1 else 0 := rfl

theorem norm_orderedNoPreservationMatrix_le (W : Finset α) (p q : ℕ)
    (hW : W.card = p + q) :
    ‖orderedNoPreservationMatrix (H := H) W p q‖ ≤
      Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ) := by
  have hrep := norm_replicatedMatrix_le (H := H)
    (tupleSubset (W := W) (p := q)) (tupleSubset (W := W) (p := p))
    q.factorial p.factorial
    (fun B => (card_filter_tupleSubset B).le) (fun B => (card_filter_tupleSubset B).le)
    (noPreservationSubsetMatrix W p q)
  calc
    _ ≤ Real.sqrt (q.factorial : ℝ) * ‖noPreservationSubsetMatrix (H := H) W p q‖ *
        Real.sqrt (p.factorial : ℝ) := hrep
    _ ≤ Real.sqrt (q.factorial : ℝ) * 1 * Real.sqrt (p.factorial : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (norm_noPreservationSubsetMatrix_le W p q hW) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Combining the square-root ordering costs never exceeds the square
root of the factorial of the total number of labels. -/
theorem sqrt_factorial_mul_sqrt_factorial_le (p q : ℕ) :
    Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ) ≤
      Real.sqrt ((p + q).factorial : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (p + q))
    (Nat.factorial_mul_factorial_dvd_factorial_add p q)

theorem norm_orderedNoPreservationMatrix_le_sqrt_factorial (W : Finset α) (p q : ℕ)
    (hW : W.card = p + q) :
    ‖orderedNoPreservationMatrix (H := H) W p q‖ ≤ Real.sqrt ((p + q).factorial : ℝ) :=
  (norm_orderedNoPreservationMatrix_le W p q hW).trans
    (sqrt_factorial_mul_sqrt_factorial_le p q)

theorem preservation_scalar_sqrt_le (p q : ℕ) :
    Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) ≤ (p + q + 1 : ℝ) := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · push_cast
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [sq_nonneg (p : ℝ), sq_nonneg (q : ℝ)]

/-- The coarser form used when summing preservation cuts of the same word. -/
theorem norm_orderedPreservationMatrix_le_sqrt_factorial (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H)
    (he : ∀ a, IsStarProjection (e a)) (horth : ∀ a b, a ≠ b → e a * e b = 0)
    (P : H →L[ℂ] H) (hP : IsStarProjection P) {d : ℝ} (hd : 0 < d) :
    ‖orderedPreservationMatrix W hW e P d‖ ≤
      Real.sqrt ((p + q).factorial : ℝ) * (1 + (p + q + 1 : ℝ) / d) := by
  apply (norm_orderedPreservationMatrix_le W hW e he horth P hP hd).trans
  apply mul_le_mul (sqrt_factorial_mul_sqrt_factorial_le p q)
  · exact add_le_add le_rfl
      (div_le_div_of_nonneg_right (preservation_scalar_sqrt_le p q) hd.le)
  · positivity
  · exact Real.sqrt_nonneg _

end

end KadisonKastler

end OAI
