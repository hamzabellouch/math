import OAI.Combinatorics.CompleteCrossing.Interpolation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! Even triangular interpolation and unisolvence. -/

section

/-! The even two-triangle set, as actual ordered interpolation coordinates. -/
noncomputable section
namespace Paper170

theorem mem_evenTriangle (s : ℕ) (p q : Fin (2*s)) :
    (p,q) ∈ evenTriangle s ↔
      (p.val < s ∧ q < p) ∨ (s ≤ p.val ∧ p < q) := by
  simp [evenTriangle]

def evenTriangleOffDiagEquiv (s : ℕ) :
    EvenTriangleCoord s ≃ ↥((Finset.univ : Finset (Fin s)).offDiag) where
  toFun pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq := (mem_evenTriangle s p q).mp hpq
    by_cases h : p.val < s
    · exact ⟨(⟨p.val, h⟩, ⟨q.val, by rcases hpq with hq | hq <;> omega⟩), by
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, ne_eq, Fin.mk.injEq]
        rcases hpq with hq | hq <;> omega⟩
    · exact ⟨(⟨p.val-s, by omega⟩, ⟨q.val-s, by omega⟩), by
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, ne_eq, Fin.mk.injEq]
        rcases hpq with hq | hq <;> omega⟩
  invFun pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq : p ≠ q := (Finset.mem_offDiag.mp hpq).2.2
    by_cases h : q < p
    · exact ⟨(⟨p.val, by omega⟩, ⟨q.val, by omega⟩),
        (mem_evenTriangle s _ _).mpr (Or.inl ⟨p.isLt,h⟩)⟩
    · exact ⟨(⟨p.val+s, by omega⟩, ⟨q.val+s, by omega⟩),
        (mem_evenTriangle s _ _).mpr (Or.inr ⟨by change s ≤ p.val+s; omega,by
          have hpq := Fin.val_ne_of_ne hpq
          change p.val+s < q.val+s
          omega⟩)⟩
  left_inv pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    have hpq := (mem_evenTriangle s p q).mp hpq
    apply Subtype.ext
    dsimp
    split_ifs with h h' h'
    · rfl
    · change ¬q.val < p.val at h'
      simp only [Fin.lt_def] at hpq
      omega
    · change q.val-s < p.val-s at h'
      simp only [Fin.lt_def] at hpq
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;>
        simp only [Fin.lt_def] at hpq <;> omega
  right_inv pq := by
    obtain ⟨⟨p,q⟩, hpq⟩ := pq
    apply Subtype.ext
    dsimp
    split_ifs with h h' h'
    · rfl
    · change ¬p.val < s at h'
      omega
    · change p.val+s < s at h'
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

theorem even_triangle_card (s : ℕ) : (evenTriangle s).card = s*(s-1) := by
  have hc := Fintype.card_congr (evenTriangleOffDiagEquiv s)
  simp only [EvenTriangleCoord, Fintype.card_coe] at hc
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hc
  simpa only [Nat.mul_sub_left_distrib, mul_one] using hc

end Paper170

end
end

section

/-! Even-node interpolation by adjoining one fresh node to the checked odd-node theorem. -/
noncomputable section
open PolynomialModule
open Zarankiewicz
namespace Paper170

theorem biBounded_mulRoot {r s : ℕ} {P : BiPoly} (hP : BiBounded r s P) (t : ℝ) :
    BiBounded (r+1) s (mulRoot t P) := by
  refine ⟨bounded_mulRoot t hP.1, ?_⟩
  intro a
  cases a with
  | zero =>
    rw [mulRoot_coeff_zero]
    exact (boundedSpace s).smul_mem _ (hP.2 0)
  | succ a =>
    rw [mulRoot_coeff_succ]
    exact bounded_sub (hP.2 a) ((boundedSpace s).smul_mem _ (hP.2 (a+1)))

theorem insertNode_injective {n : ℕ} (r : Fin (n+1)) (node : Fin n → ℝ)
    (hn : Function.Injective node) (t : ℝ) (ht : ∀i, node i ≠ t) :
    Function.Injective (Fin.insertNth r t node) := by
  intro a b
  refine Fin.succAboveCases r ?_ (fun a => ?_) a
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · intro
      rfl
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro h
      exact (ht b h.symm).elim
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro h
      exact (ht a h).elim
    · simp only [Fin.insertNth_apply_succAbove]
      intro h
      exact congrArg r.succAbove (hn h)

theorem oddTriangle_unisolvent_fin (s : ℕ) (node : Fin (2*s+1) → ℝ)
    (hn : Function.Injective node) (P : BiPoly) (hP : BiBounded s s P)
    (hv : ∀a b : Fin (2*s+1),
      (b < a ∧ a.val ≤ s) ∨ (s < a.val ∧ a < b) → biEval (node a) (node b) P = 0) :
    P = 0 := by
  let x : ℕ → ℝ := fun k => if h : 1 ≤ k ∧ k ≤ 2*s+1 then node ⟨k-1,by omega⟩ else 0
  have hx : Set.InjOn x (Set.Icc 1 (2*s+1)) := by
    intro a ha b hb he
    simp only [Set.mem_Icc] at ha hb
    simp only [x, dite_eq_left ha, dite_eq_left hb] at he
    have := congrArg Fin.val (hn he)
    dsimp at this
    omega
  apply twoTriangle_unisolvent s x hx P hP
  intro a b hab
  rw [mem_twoTriangle] at hab
  have ha : 1 ≤ a ∧ a ≤ 2*s+1 := by omega
  have hb : 1 ≤ b ∧ b ≤ 2*s+1 := by omega
  simp only [x, dite_eq_left ha, dite_eq_left hb]
  apply hv
  change (b-1 < a-1 ∧ a-1 ≤ s) ∨ (s < a-1 ∧ a-1 < b-1)
  omega

theorem evenTriangle_unisolvent_first (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded s (s-1) P)
    (hv : ∀a b, (a,b) ∈ evenTriangle s → biEval (node a) (node b) P = 0) : P = 0 := by
  obtain ⟨t,ht⟩ := (Set.finite_range node).exists_notMem
  have hnt : ∀i, node i ≠ t := fun i h => ht ⟨i,h⟩
  let x : Fin (2*s+1) → ℝ := Fin.insertNth (0 : Fin (2*s+1)) t node
  let Q := swapBi (mulRoot t (swapBi P))
  have hQ : BiBounded s s Q := by
    have hb := biBounded_swap (biBounded_mulRoot (biBounded_swap hP) t)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using hb
  have hev (u v : ℝ) : biEval u v Q = (v-t)*biEval u v P := by
    simp only [Q, biEval_swap, biEval_mulRoot]
  have hzero : Q = 0 := by
    apply oddTriangle_unisolvent_fin s x (insertNode_injective _ node hn t hnt) Q hQ
    intro a b
    refine Fin.succAboveCases (0 : Fin (2*s+1)) ?_ (fun a => ?_) a
    · intro h
      have : False := by simp only [Fin.lt_def, Fin.val_zero] at h; omega
      exact this.elim
    · refine Fin.succAboveCases (0 : Fin (2*s+1)) ?_ (fun b => ?_) b
      · intro _
        simp only [hev, x, Fin.insertNth_apply_same, sub_self, zero_mul]
      · intro hab
        simp only [x, Fin.insertNth_apply_succAbove, hev]
        rw [hv a b]
        · exact mul_zero _
        · rw [mem_evenTriangle]
          simp only [Fin.succAbove_zero, Fin.val_succ, Fin.lt_def] at hab
          simp only [Fin.lt_def]
          omega
  have hroot : mulRoot t (swapBi P) = 0 := by
    apply swapBi.injective
    simpa only [map_zero] using hzero
  have hpzero := eq_zero_of_mulRoot_eq_zero t (s-1) (swapBi P) (biBounded_swap hP).1 hroot
  apply swapBi.injective
  simpa only [map_zero] using hpzero

theorem evenTriangle_unisolvent_second (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded (s-1) s P)
    (hv : ∀a b, (a,b) ∈ evenTriangle s → biEval (node a) (node b) P = 0) : P = 0 := by
  obtain ⟨t,ht⟩ := (Set.finite_range node).exists_notMem
  have hnt : ∀i, node i ≠ t := fun i h => ht ⟨i,h⟩
  let r : Fin (2*s+1) := ⟨s,by omega⟩
  let x : Fin (2*s+1) → ℝ := Fin.insertNth r t node
  have hQ : BiBounded s s (mulRoot t P) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using biBounded_mulRoot hP t
  apply eq_zero_of_mulRoot_eq_zero t (s-1) P hP.1
  apply oddTriangle_unisolvent_fin s x (insertNode_injective r node hn t hnt) _ hQ
  intro a b
  refine Fin.succAboveCases r ?_ (fun a => ?_) a
  · intro _
    simp only [biEval_mulRoot, x, Fin.insertNth_apply_same, sub_self, zero_mul]
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · intro hab
      have : False := by
        simp only [Fin.lt_def, r] at hab
        omega
      exact this.elim
    · intro hab
      simp only [x, Fin.insertNth_apply_succAbove, biEval_mulRoot]
      rw [hv a b]
      · exact mul_zero _
      · rw [mem_evenTriangle]
        simp only [Fin.lt_def, r, Fin.succAbove, Fin.val_castSucc] at hab
        simp only [Fin.lt_def]
        split_ifs at hab <;> simp only [Fin.val_castSucc, Fin.val_succ] at hab <;> omega

end Paper170

end
end

section

/-! Bijective interpolation on both even-node degree rectangles. -/
noncomputable section
namespace Paper170

theorem evenTriangle_vanish_first (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P ∈ rectangle (s-1) (s-2))
    (hv : ∀a b, (a,b) ∈ evenTriangle s → evalTwo (node a) (node b) P = 0) : P = 0 := by
  apply toBiPolynomial.injective
  rw [map_zero]
  apply evenTriangle_unisolvent_first s hs node hn (toBiPolynomial P)
  · convert toBiPolynomial_bounded (s-1) (s-2) P hP using 1 <;> omega
  · intro a b hab
    rw [toBiPolynomial_eval]
    exact hv a b hab

theorem evenTriangle_vanish_second (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P ∈ rectangle (s-2) (s-1))
    (hv : ∀a b, (a,b) ∈ evenTriangle s → evalTwo (node a) (node b) P = 0) : P = 0 := by
  apply toBiPolynomial.injective
  rw [map_zero]
  apply evenTriangle_unisolvent_second s hs node hn (toBiPolynomial P)
  · convert toBiPolynomial_bounded (s-2) (s-1) P hP using 1 <;> omega
  · intro a b hab
    rw [toBiPolynomial_eval]
    exact hv a b hab

theorem triangleEvaluation_bijective_of_unisolvent (s a b : ℕ) (node : Fin (2*s) → ℝ)
    (hdim : (a+1)*(b+1) = s*(s-1))
    (hv : ∀P ∈ rectangle a b,
      (∀i j, (i,j) ∈ evenTriangle s → evalTwo (node i) (node j) P = 0) → P=0) :
    Function.Bijective (triangleEvaluation s a b node) := by
  let := rectangle_finite a b
  have hi : Function.Injective (triangleEvaluation s a b node) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    apply hv P.val P.property
    intro i j hij
    exact congrFun hP ⟨(i,j),hij⟩
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  rw [rectangle_dimension, Module.finrank_fintype_fun_eq_card]
  have hc : Fintype.card (EvenTriangleCoord s) = s*(s-1) := by
    rw [Fintype.card_coe, even_triangle_card]
  rw [hc,hdim]

theorem two_triangle_interpolation (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) :
    Function.Bijective (triangleEvaluation s (s-1) (s-2) node) ∧
      Function.Bijective (triangleEvaluation s (s-2) (s-1) node) := by
  constructor
  · apply triangleEvaluation_bijective_of_unisolvent
    · congr 1 <;> omega
    · exact evenTriangle_vanish_first s hs node hn
  · apply triangleEvaluation_bijective_of_unisolvent
    · rw [Nat.mul_comm]
      congr 1 <;> omega
    · exact evenTriangle_vanish_second s hs node hn

end Paper170

end
end

end OAI
