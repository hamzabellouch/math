import OAI.NumberTheory.Ostmann.Arithmetic.RealSlotEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSizes

namespace OAI

/-! # Polynomial dependence on one original bulk-prime slot -/

namespace Ostmann
open scoped Classical

/-- A bulk coordinate never occurs in any compensation denominator. -/
def MovingSlotData.CompensationAbsent {σ : Type*} (i : σ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ u left right =>
      i ∉ u ∧ left.CompensationAbsent i ∧ right.CompensationAbsent i

theorem MovingSlotData.compensationAbsent_of_levels {σ : Type*}
    (tier : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.Levels tier) (i : σ) (hi : n ≤ tier i) : T.CompensationAbsent i := by
  induction T with
  | leaf => trivial
  | @node n s CL CR u left right ihL ihR =>
    refine ⟨?_, ihL hT.2.2.2.1 (by omega), ihR hT.2.2.2.2 (by omega)⟩
    intro hu
    have := hT.2.2.1 i hu
    omega

noncomputable def bulkSlotProduct {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) : Polynomial ℝ :=
  (slots.map (fun j => if j = i then Polynomial.X else Polynomial.C (value j))).prod

theorem bulkSlotProduct_eval {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) (p : ℝ) :
    (bulkSlotProduct value i slots).eval p =
      realSlotProduct (Function.update value i p) slots := by
  induction slots with
  | nil => simp [bulkSlotProduct, realSlotProduct]
  | cons j slots ih =>
    by_cases hji : j = i
    · subst j
      simp only [bulkSlotProduct, List.map_cons, List.prod_cons, Polynomial.eval_mul,
        ite_true, Polynomial.eval_X, realSlotProduct,
        Function.update_self] at *
      exact congrArg (p * ·) ih
    · simp only [bulkSlotProduct, List.map_cons, List.prod_cons, Polynomial.eval_mul,
        ite_eq_right hji, Polynomial.eval_C, realSlotProduct,
        Function.update_of_ne hji] at *
      exact congrArg (value j * ·) ih

theorem bulkSlotProduct_degree {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) : (bulkSlotProduct value i slots).natDegree ≤ slots.length := by
  induction slots with
  | nil => simp [bulkSlotProduct]
  | cons j slots ih =>
    change ((if j = i then Polynomial.X else Polynomial.C (value j)) *
      bulkSlotProduct value i slots).natDegree ≤ slots.length + 1
    have hj : (if j = i then Polynomial.X else Polynomial.C (value j)).natDegree ≤ 1 := by
      split_ifs <;> simp
    exact Polynomial.natDegree_mul_le.trans (by omega)

theorem realSlotProduct_update_of_absent {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) (hi : i ∉ slots) (p : ℝ) :
    realSlotProduct (Function.update value i p) slots =
      realSlotProduct value slots := by
  unfold realSlotProduct
  congr 1
  apply List.map_congr_left
  intro j hj
  apply Function.update_of_ne
  intro h
  subst j
  exact hi hj

noncomputable def MovingSlotReversal.bulkPivotPolynomial {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ)
    (L R : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (((s.rootFrequency : ℝ) *
    realSlotProduct value s.compensationSlots)⁻¹) *
    (Polynomial.C (s.leftFrequency : ℝ) * bulkSlotProduct value i s.rightSlots * R -
      Polynomial.C (s.rightFrequency : ℝ) * bulkSlotProduct value i s.leftSlots * L)

theorem MovingSlotReversal.bulkPivotPolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ)
    (hi : i ∉ s.compensationSlots) (L R : Polynomial ℝ) (p : ℝ) :
    (s.bulkPivotPolynomial value i L R).eval p =
      s.realValuePivot (Function.update value i p) (L.eval p) (R.eval p) := by
  simp only [bulkPivotPolynomial, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    bulkSlotProduct_eval, realValuePivot, realSlotProduct_update_of_absent value i _ hi, div_eq_mul_inv]
  ring

theorem MovingSlotReversal.bulkPivotPolynomial_degree {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ)
    (L R : Polynomial ℝ) (d e : ℕ) (hs : s.lengthLE d)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    (s.bulkPivotPolynomial value i L R).natDegree ≤ d + e := by
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_C, zero_add] using
          (bulkSlotProduct_degree value i s.rightSlots).trans hs.1)) hR)
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_C, zero_add] using
          (bulkSlotProduct_degree value i s.leftSlots).trans hs.2.1)) hL)

end Ostmann

end OAI
