import OAI.NumberTheory.Ostmann.Arithmetic.RealNodeSupport
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotPolynomials
import OAI.NumberTheory.Ostmann.Characters.PolynomialCellSupports

namespace OAI

/-! # Exact polynomial inequalities for all original bulk node supports -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.bulkCompositePolynomial {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ) (L R : Polynomial ℝ) : Polynomial ℝ :=
  { s with compensationSlots := [] }.bulkPivotPolynomial value i L R

theorem MovingSlotReversal.bulkCompositePolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ) (L R : Polynomial ℝ) (z : ℝ) :
    (s.bulkCompositePolynomial value i L R).eval z =
      s.realCompositePivot (Function.update value i z) (L.eval z) (R.eval z) := by
  rw [bulkCompositePolynomial, bulkPivotPolynomial_eval _ _ _ (by simp) L R z]
  simp only [realValuePivot, realCompositePivot, realSlotProduct, List.map_nil, List.prod_nil, mul_one]

theorem MovingSlotReversal.bulkCompositePolynomial_degree {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ) (L R : Polynomial ℝ)
    (d e : ℕ) (hs : s.lengthLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    (s.bulkCompositePolynomial value i L R).natDegree ≤ d + e :=
  bulkPivotPolynomial_degree _ value i L R d e ⟨hs.1, hs.2.1, by simp⟩ hL hR

noncomputable def MovingSlotData.bulkNodeSupportPolynomials {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ)
  | _, .leaf _ _, _, _ => []
  | n + 1, .node s CL CR u left right, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let Q := step.bulkCompositePolynomial value i L R
      let p := step.bulkPivotPolynomial value i L R
      [Q - Polynomial.C 1, Polynomial.C (pivotBound (n + 1) : ℝ) - Q,
        R * bulkSlotProduct value i CR -
          Polynomial.C ((2 * pivotBound (n + 1) * childBound (n + 1) + 1 : ℕ) : ℝ)] ++
        (left.bulkNodeSupportPolynomials value i childBound pivotBound p L ++
          right.bulkNodeSupportPolynomials value i childBound pivotBound p R)

theorem MovingSlotData.bulkNodeSupportPolynomials_eval {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (z : ℝ) :
    (∀ P ∈ T.bulkNodeSupportPolynomials value i childBound pivotBound L R, 0 ≤ P.eval z) ↔
      realValueNodeSupport (Function.update value i z) childBound pivotBound T (L.eval z) (R.eval z) := by
  induction T generalizing L R with
  | leaf => simp [bulkNodeSupportPolynomials, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_eval
      value i hT.1 L R z
    simp only [bulkNodeSupportPolynomials, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, bulkSlotProduct_eval,
      MovingSlotReversal.bulkCompositePolynomial_eval,
      ihL hT.2.1, ihR hT.2.2, hp, realValueNodeSupport, sub_nonneg]
    tauto

theorem MovingSlotData.bulkNodeSupportPolynomials_length {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) :
    (T.bulkNodeSupportPolynomials value i childBound pivotBound L R).length = 3 * (2 ^ n - 1) := by
  induction T generalizing L R with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [bulkNodeSupportPolynomials, List.length_append, List.length_cons,
      List.length_nil, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- Every inequality has degree bounded by the depth times the actual slot
length. No coefficient-size assumption is needed. -/
theorem MovingSlotData.bulkNodeSupportPolynomials_degree {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d e : ℕ)
    (hsize : T.SizeLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∀ P ∈ T.bulkNodeSupportPolynomials value i childBound pivotBound L R, P.natDegree ≤ n * d + e := by
  induction T generalizing L R e with
  | leaf => simp [bulkNodeSupportPolynomials]
  | @node n s CL CR u left right ihL ihR =>
    have hs : (MovingSlotData.step s CL CR u left right false).lengthLE d :=
      ⟨hsize.2.1, hsize.1, hsize.2.2.1⟩
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_degree
      value i L R d e hs hL hR
    have hQ := (MovingSlotData.step s CL CR u left right false).bulkCompositePolynomial_degree
      value i L R d e hs hL hR
    have hLR := Polynomial.natDegree_mul_le (p := R) (q := bulkSlotProduct value i CR)
    have hCR := (bulkSlotProduct_degree value i CR).trans hsize.2.1
    have hLe : L.natDegree ≤ d + e := hL.trans (Nat.le_add_left _ _)
    have hRe : R.natDegree ≤ d + e := hR.trans (Nat.le_add_left _ _)
    have hn : n * d + (d + e) = (n + 1) * d + e := by ring
    intro P hP
    simp only [bulkNodeSupportPolynomials, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hP
    rcases hP with (rfl | rfl | rfl) | hP | hP
    · have hd := Polynomial.natDegree_sub_le
        ((MovingSlotData.step s CL CR u left right false).bulkCompositePolynomial value i L R) (Polynomial.C 1)
      simp only [Polynomial.natDegree_C, max_zero] at hd
      exact hd.trans (hQ.trans (by omega))
    · have hd := Polynomial.natDegree_sub_le (Polynomial.C (pivotBound (n + 1) : ℝ))
        ((MovingSlotData.step s CL CR u left right false).bulkCompositePolynomial value i L R)
      simp only [Polynomial.natDegree_C, zero_max] at hd
      exact hd.trans (hQ.trans (by omega))
    · have hd := Polynomial.natDegree_sub_le (R * bulkSlotProduct value i CR)
        (Polynomial.C ((2 * pivotBound (n + 1) * childBound (n + 1) + 1 : ℕ) : ℝ))
      simp only [Polynomial.natDegree_C, max_zero] at hd
      exact hd.trans (hLR.trans (by omega))
    · simpa only [hn] using ihL _ _ (d + e) hsize.2.2.2.1 hp hLe P hP
    · simpa only [hn] using ihR _ _ (d + e) hsize.2.2.2.2 hp hRe P hP

end Ostmann

end OAI
