import OAI.Combinatorics.CompleteCrossing.Triangle
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Order-detecting interpolation and its kernel. -/

section

/-! The order pairing as a nonzero diagonal pairing on the even two-triangle set. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def evenTriangleWeight (s : ℕ) (node : Fin (2*s) → ℝ) (a : EvenTriangleCoord s) : ℝ :=
  (if a.val.1.val < s then -1 else 1) * (node a.val.1-node a.val.2) /
    (Zarankiewicz.derivativeAtNode node a.val.1 * Zarankiewicz.derivativeAtNode node a.val.2)

theorem evenTriangleWeight_ne_zero (s : ℕ) (node : Fin (2*s) → ℝ)
    (hn : Function.Injective node) (a : EvenTriangleCoord s) : evenTriangleWeight s node a ≠ 0 := by
  have ha := (mem_evenTriangle s a.val.1 a.val.2).mp a.property
  have hne : a.val.1 ≠ a.val.2 := by rcases ha with ha | ha; exact ne_of_gt ha.2; exact ne_of_lt ha.2
  unfold evenTriangleWeight
  apply div_ne_zero
  · apply mul_ne_zero
    · split_ifs <;> norm_num
    · exact sub_ne_zero.mpr (hn.ne hne)
  · exact mul_ne_zero (Zarankiewicz.derivativeAtNode_ne_zero node hn _)
      (Zarankiewicz.derivativeAtNode_ne_zero node hn _)

theorem shifted_halfOrder (s : ℕ) (node : Fin (2*s) → ℝ) (p q : Fin (2*s)) :
    (halfOrder inferInstance p q + (if p.val < s then -(1/2) else 1/2)) * (node p-node q) =
      if (p,q) ∈ evenTriangle s then
        (if p.val < s then -1 else 1) * (node p-node q) else 0 := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have hqp := not_lt_of_ge (le_of_lt hpq)
    by_cases hp : p.val < s <;>
      simp [halfOrder, hpq, hqp, mem_evenTriangle, hp, not_lt.mp]
    ring
  · simp [halfOrder]
  · have hpq := not_lt_of_ge (le_of_lt hqp)
    by_cases hp : p.val < s <;>
      simp [halfOrder, hpq, hqp, mem_evenTriangle, hp, not_lt.mp]
    ring

theorem orderPairing_triangle (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) (A B : Poly2)
    (hA : A ∈ rectangle (s-1) (s-2)) (hB : B ∈ rectangle (s-2) (s-1)) :
    orderPairing node inferInstance A B = ∑ a : EvenTriangleCoord s,
      evenTriangleWeight s node a * evalTwo (node a.val.1) (node a.val.2) A *
        evalTwo (node a.val.1) (node a.val.2) B := by
  have hshift := pairing_row_column_invariant s hs (by simp) node hn (halfOrder inferInstance)
    (fun p => if p.val < s then -(1/2) else 1/2) (fun _ => 0) A B hA hB
  simp only [add_zero] at hshift
  rw [orderPairing, ← hshift]
  let F (a : Fin (2*s) × Fin (2*s)) : ℝ :=
    (if a.1.val < s then -1 else 1) * (node a.1-node a.2) /
      (Zarankiewicz.derivativeAtNode node a.1 * Zarankiewicz.derivativeAtNode node a.2) *
      evalTwo (node a.1) (node a.2) A * evalTwo (node a.1) (node a.2) B
  change _ = ∑ a : EvenTriangleCoord s, F a.val
  calc
    _ = ∑ a ∈ evenTriangle s, F a := by
      unfold weightedPairing
      simp_rw [shifted_halfOrder]
      rw [evenTriangle, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      by_cases ha : (p,q) ∈ evenTriangle s
      · have hh := (mem_evenTriangle s p q).mp ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hh, F]
      · have hh := (mem_evenTriangle s p q).not.mp ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_right hh, zero_div, zero_mul]
    _ = ∑ a : EvenTriangleCoord s, F a.val := (Finset.sum_coe_sort (evenTriangle s) F).symm

theorem derivativeAtNode_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (node : ι → ℝ) (e : κ ≃ ι) (p : κ) :
    Zarankiewicz.derivativeAtNode (node ∘ e) p = Zarankiewicz.derivativeAtNode node (e p) := by
  classical
  have h : Zarankiewicz.nodePolynomial (node ∘ e) = Zarankiewicz.nodePolynomial node := by
    unfold Zarankiewicz.nodePolynomial
    exact e.prod_comp (fun i => (Polynomial.X-Polynomial.C (node i) : Polynomial ℝ))
  simp only [Zarankiewicz.derivativeAtNode, h, Function.comp_apply]

theorem weightedPairing_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (node : ι → ℝ) (e : κ ≃ ι) (K : ι → ι → ℝ) (A B : Poly2) :
    weightedPairing (node ∘ e) (fun p q => K (e p) (e q)) A B = weightedPairing node K A B := by
  unfold weightedPairing
  simp_rw [derivativeAtNode_equiv, Function.comp_apply]
  let F (p q : ι) : ℝ := K p q * (node p-node q) /
    (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q) *
    evalTwo (node p) (node q) A * evalTwo (node p) (node q) B
  change (∑p : κ, ∑q : κ, F (e p) (e q)) = ∑p : ι, ∑q : ι, F p q
  calc
    _ = ∑p : κ, ∑q : ι, F (e p) q := by
      apply Finset.sum_congr rfl
      intro p _
      exact e.sum_comp (F (e p))
    _ = _ := e.sum_comp (fun p => ∑q, F p q)

theorem orderPairing_orderIso {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (node : ι → ℝ) (e : κ ≃o ι) (A B : Poly2) :
    orderPairing (node ∘ e) inferInstance A B = orderPairing node inferInstance A B := by
  have h : (fun p q => halfOrder inferInstance (e p) (e q)) = halfOrder (inferInstance : LinearOrder κ) := by
    funext p q
    simp only [halfOrder, e.lt_iff_lt]
  rw [orderPairing, ← h]
  exact weightedPairing_equiv node e.toEquiv _ A B

end Paper170

end
end

section

/-! Nonsingularity of the weighted half-order pairing for every node order. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem order_pairing_nonsingular_fin (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) :
    (∀ A ∈ rectangle (s-1) (s-2),
      (∀ B ∈ rectangle (s-2) (s-1), orderPairing node inferInstance A B = 0) → A=0) ∧
    (∀ B ∈ rectangle (s-2) (s-1),
      (∀ A ∈ rectangle (s-1) (s-2), orderPairing node inferInstance A B = 0) → B=0) := by
  classical
  obtain ⟨hfirst,hsecond⟩ := two_triangle_interpolation s hs node hn
  constructor
  · intro A hA hz
    apply evenTriangle_vanish_first s hs node hn A hA
    intro i j hij
    let a : EvenTriangleCoord s := ⟨(i,j),hij⟩
    obtain ⟨B,hB⟩ := hsecond.surjective (Pi.single a (1:ℝ))
    have he (b : EvenTriangleCoord s) : evalTwo (node b.val.1) (node b.val.2) B.val =
        (Pi.single a (1:ℝ) : EvenTriangleCoord s → ℝ) b := congrFun hB b
    have hzero := hz B.val B.property
    rw [orderPairing_triangle s hs node hn A B.val hA B.property] at hzero
    simp_rw [he] at hzero
    have hv : evenTriangleWeight s node a * evalTwo (node i) (node j) A = 0 := by
      simpa [Pi.single_apply, mul_ite, a] using hzero
    exact (mul_eq_zero.mp hv).resolve_left (evenTriangleWeight_ne_zero s node hn a)
  · intro B hB hz
    apply evenTriangle_vanish_second s hs node hn B hB
    intro i j hij
    let a : EvenTriangleCoord s := ⟨(i,j),hij⟩
    obtain ⟨A,hA⟩ := hfirst.surjective (Pi.single a (1:ℝ))
    have he (b : EvenTriangleCoord s) : evalTwo (node b.val.1) (node b.val.2) A.val =
        (Pi.single a (1:ℝ) : EvenTriangleCoord s → ℝ) b := congrFun hA b
    have hzero := hz A.val A.property
    rw [orderPairing_triangle s hs node hn A.val B A.property hB] at hzero
    simp_rw [he] at hzero
    have hv : evenTriangleWeight s node a * evalTwo (node i) (node j) B = 0 := by
      simpa [Pi.single_apply, mul_ite, ite_mul, a] using hzero
    exact (mul_eq_zero.mp hv).resolve_left (evenTriangleWeight_ne_zero s node hn a)

theorem order_pairing_nonsingular {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (order : LinearOrder ι) :
    (∀ A ∈ rectangle (s-1) (s-2),
      (∀ B ∈ rectangle (s-2) (s-1), orderPairing node order A B = 0) → A=0) ∧
    (∀ B ∈ rectangle (s-2) (s-1),
      (∀ A ∈ rectangle (s-1) (s-2), orderPairing node order A B = 0) → B=0) := by
  let := order
  let e : Fin (2*s) ≃o ι := Fintype.orderIsoFinOfCardEq ι hc
  obtain ⟨hfirst,hsecond⟩ := order_pairing_nonsingular_fin s hs (node ∘ e) (hn.comp e.injective)
  constructor
  · intro A hA hz
    apply hfirst A hA
    intro B hB
    rw [orderPairing_orderIso node e]
    exact hz B hB
  · intro B hB hz
    apply hsecond B hB
    intro A hA
    rw [orderPairing_orderIso node e]
    exact hz A hA

theorem order_detector {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (order : LinearOrder ι)
    (A : Poly2) (hA : A ∈ rectangle (s-2) (s-2))
    (hzero : ∀ B ∈ rectangle (s-1) (s-1), orderPairing node order A B = 0) : A=0 := by
  apply (order_pairing_nonsingular s hs hc node hn order).1 A
  · rw [rectangle_membership] at hA ⊢
    exact ⟨hA.1.trans (by omega), hA.2⟩
  · intro B hB
    apply hzero B
    rw [rectangle_membership] at hB ⊢
    exact ⟨hB.1.trans (by omega), hB.2⟩

end Paper170

end
end

end OAI
