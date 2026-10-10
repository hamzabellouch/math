import OAI.MeasureTheory.Falconer.Recursion.Potential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer
open Finset

noncomputable def intervalMin (A : ℕ → ℝ) (a t : ℕ) : ℝ :=
  finiteMin (Finset.Icc a t) A

noncomputable def height (A : ℕ → ℝ) (a p : ℕ) : ℝ :=
  A p - intervalMin A a p

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

theorem height_nonneg (A : ℕ → ℝ) {a p : ℕ} (hap : a ≤ p) :
    0 ≤ height A a p := sub_nonneg.mpr (intervalMin_le A hap le_rfl)

theorem policy_prefix_payment (A : ℕ → ℝ) {a p v t l r q : ℕ}
    (hq : 0 < q) (hw : p+10*q ≤ v) (hap : a ≤ p) (hvt : v ≤ t)
    (hlp : l ≤ p) (htr : t ≤ r+2*q)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a t (10*q) + height A a p ≤ potential A p v (10*q) := by
  obtain ⟨i,hai,hip,hmin⟩ := intervalMin_attained A hap
  unfold height
  rw [hmin]
  apply prefix_payment A (by omega) hw hai hip hvt
  intro n hpn hnv
  exact hinner n (by omega) (by omega)

theorem policy_suffix_payment (A : ℕ → ℝ) {a p t l r q : ℕ}
    (hq : 0 < q) (hw : a+10*q ≤ p) (hpt : p ≤ t)
    (hla : l ≤ a+2*q) (hpr : p ≤ r)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a t (10*q) + (A p - intervalMin A p t) ≤
      potential A a p (10*q) := by
  obtain ⟨j,hpj,hjt,hmin⟩ := intervalMin_attained A hpt
  rw [hmin]
  apply suffix_payment A (by omega) hw hpj hjt
  intro n han hnp
  exact hinner n (by omega) (by omega)

theorem policy_direct_payment (A : ℕ → ℝ) {a p v b u l r L q : ℕ}
    (hq : 0 < q) (hw : p+10*q ≤ v) (hap : a ≤ p)
    (hlp : l ≤ p) (hpr : p ≤ r) (hl : l ≤ b+2*q) (hr : u ≤ r+2*q)
    (hLu : b+2*L ≤ u) (hv : v ≤ a+2*L)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a v (10*q) + height A a p ≤ potential A p v (10*q) := by
  obtain ⟨i,hai,hip,hmin⟩ := intervalMin_attained A hap
  by_cases hcost : 0 < height A a p
  · have hi : A i < A p := by unfold height at hcost; rw [hmin] at hcost; linarith
    simpa only [height, hmin] using
      direct_origin_payment A hq rfl hw hai hip hlp hpr hl hr hLu hv hi hinner
  · have hz : height A a p = 0 := le_antisymm (not_lt.mp hcost) (height_nonneg A hap)
    rw [hz, add_zero]
    exact potential_mono A (by omega) hw hap le_rfl

theorem branch_cost_bound (V C : ℕ → ℝ) (n : ℕ)
    (hpay : ∀ k < n, V k + C k ≤ V (k+1)) :
    ∑ k ∈ Finset.range n, C k ≤ V n - V 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs := ih (fun k hk => hpay k (by omega))
    have hn := hpay n (by omega)
    linarith

theorem profile_increments_telescope (A : ℕ → ℝ) (start : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range n, -2 * (A (start (k+1)) - A (start k)) =
      2*A (start 0) - 2*A (start n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem nearby_pair {a t f Q : ℕ} (hQ : 0 < Q) (hw : a+Q ≤ t)
    (haf : a ≤ f) (hft : f ≤ t) :
    ∃ i j, a ≤ i ∧ i < j ∧ j ≤ t ∧ i+Q = j ∧
      i ≤ f ∧ f ≤ j ∧ f ≤ i+Q ∧ j ≤ f+Q := by
  refine ⟨max a (f-Q), max a (f-Q)+Q, ?_⟩
  omega

theorem potential_near_final (A : ℕ → ℝ) {a t f Q : ℕ} {e : ℝ}
    (hQ : 0 < Q) (hw : a+Q ≤ t) (haf : a ≤ f) (hft : f ≤ t)
    (hlocal : ∀ i, a ≤ i → i ≤ t → i ≤ f+Q → f ≤ i+Q → A i ≤ A f+e) :
    potential A a t Q ≤ 2*A f+2*e := by
  obtain ⟨i,j,hai,hij,hjt,hgap,hif,hfj,hfi,hjf⟩ := nearby_pair hQ hw haf hft
  have hp := potential_le A (Q := Q) hai hij hjt (by omega)
  have hi := hlocal i hai (by omega) (by omega) hfi
  have hj := hlocal j (by omega) hjt hjf (by omega)
  linarith

theorem branch_exponent_bound (A : ℕ → ℝ) (start : ℕ → ℕ)
    (V C loss : ℕ → ℝ) (n : ℕ) (e terminal lossBound : ℝ)
    (hpay : ∀ k < n, V k + C k ≤ V (k+1))
    (hfinal : V n ≤ 2*A (start n)+e)
    (hloss : ∑ k ∈ Finset.range n, loss k ≤ lossBound) :
    (∑ k ∈ Finset.range n,
       (-2*(A (start (k+1))-A (start k)) + C k + loss k)) + terminal ≤
      2*A (start 0)-V 0+e+lossBound+terminal := by
  simp only [Finset.sum_add_distrib]
  rw [profile_increments_telescope]
  have hc := branch_cost_bound V C n hpay
  linarith

end PlanarFalconer

end OAI
