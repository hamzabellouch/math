import OAI.NumberTheory.TwoPoint.Walks.RetainedComplexEdges
import OAI.NumberTheory.TwoPoint.Bounds.SymmetricEdgeTesting

namespace OAI

/-! The exact symmetric retained matrix for arbitrary complex tests. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma retainedRealEdge_reverse_test (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hg : ∀ z, g z ≠ 0) (F G : ℤ → ℂ) :
    star (retainedComplexScalar g keep (fun z => star (F z)) n) *
        (directedIntegerEdge Q u eligible g center L K extra h d q m n : ℂ) *
        retainedComplexScalar g keep G m =
      F n * G m * (retainedRealEdge Q u eligible g center L K extra keep h d q m n : ℂ) := by
  have ht := retainedRealEdge_test Q u eligible g center L K extra keep h d q m n hg
    (fun _ => F n) (fun _ => G m)
  by_cases hn : keep n <;> by_cases hm : keep m
  · simp only [retainedComplexScalar, hn, hm, ite_true, star_mul, star_star] at ht ⊢
    have hgn : star (g n : ℂ) = (g n : ℂ) := by simp
    have hgm : star (g m : ℂ) = (g m : ℂ) := by simp
    rw [hgn]
    rw [hgm] at ht
    convert ht using 1; ring
  all_goals simp [retainedComplexScalar, retainedRealEdge, hn, hm]

noncomputable def retainedDirectedMatrix {V : Type*} (site : V → ℤ)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) : Matrix V V ℂ := fun i j =>
  if gate i j then ∑ q ∈ Q,
    (retainedRealEdge Q u eligible g center L K extra keep h d q (site i) (site j) : ℂ)
  else 0

theorem retained_matrix_bilinear {V : Type*} [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (hg : ∀ z, g z ≠ 0) (F G : ℤ → ℂ) :
    let vf := WithLp.toLp 2 (fun i => retainedComplexScalar g keep (fun z => star (F z)) (site i))
    let vg := WithLp.toLp 2 (fun i => retainedComplexScalar g keep G (site i))
    let A := retainedDirectedMatrix site Q u eligible g center L K extra keep h d gate
    inner ℂ vf (matrixOperator (maskedIntegerEdgeMatrix site Q u eligible
      g center L K extra h d gate) vg) =
      ∑ i, ∑ j, F (site i) * G (site j) * (A i j + A j i) := by
  dsimp only
  change (∑ i, (∑ j, maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j *
      retainedComplexScalar g keep G (site j)) *
        star (retainedComplexScalar g keep (fun z => star (F z)) (site i))) = _
  simp only [sum_mul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [maskedIntegerEdgeMatrix_directed site Q u eligible g center L K extra h d gate hgate]
  unfold retainedDirectedMatrix
  by_cases hij : gate i j
  · have hji := (hgate i j).mp hij
    simp only [hij, hji, ite_true, Complex.ofReal_add, Complex.ofReal_sum,
      add_mul, sum_mul, mul_add, mul_sum]
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro q _
    have hf := retainedRealEdge_test Q u eligible g center L K extra keep h d q
      (site i) (site j) hg F G
    have hr := retainedRealEdge_reverse_test Q u eligible g center L K extra keep h d q
      (site i) (site j) hg F G
    linear_combination hf + hr
  · have hji : ¬gate j i := fun h => hij ((hgate i j).mpr h)
    simp [hij, hji]

end TwoPointCorrelations

end OAI
