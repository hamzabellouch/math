import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Prime tuples in the marginal floor error

Fix the first `h` entries of an ordered prime tuple and count the last
entry by a Chebyshev bound. Summing its reciprocal-product weight gives
the `h`th power of the reciprocal-prime sum. Repeated primes are allowed,
so this bounds the distinct tuples used in inclusion-exclusion as well.
The Chebyshev and reciprocal-sum hypotheses are explicit arithmetic inputs.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

/-- Only the range `t ≥ y` of the usual Chebyshev upper estimate is needed. -/
def PrimeCountingUpperBound (C y : ℝ) : Prop :=
  ∀ t : ℝ, y ≤ t → (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / Real.log t

/-- Allowed large primes up to the real endpoint `N`. -/
noncomputable def largePrimeSet (N y : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊N⌋₊).filter (fun p => y < (p : ℝ))

/-- Ordered tuples of `h` primes from `P` with product at most `N`. -/
noncomputable def primeTupleCount (P : Finset ℕ) (h : ℕ) (N : ℝ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin h => P).filter
    (fun f => (∏ i, (f i : ℝ)) ≤ N)).card

private theorem card_filter_product_real {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β)
    (Q : α → β → Prop) [∀ a, DecidablePred (Q a)] :
    (((A.product B).filter (fun ab => Q ab.1 ab.2)).card : ℝ) =
      ∑ a ∈ A, ((B.filter (Q a)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  exact Finset.sum_product' A B (fun a b => ((if Q a b then 1 else 0 : ℕ) : ℝ))

/-- The one-dimensional final-coordinate estimate. -/
theorem prime_product_fiber_bound {P : Finset ℕ} {C y N r : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ y < (p : ℝ)) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hr : 0 < r)
    (hcount : PrimeCountingUpperBound C y) :
    ((P.filter (fun p : ℕ => r * (p : ℝ) ≤ N)).card : ℝ) ≤
      (C * N / Real.log y) * (1 / r) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  by_cases ht : y ≤ N / r
  · have hsub : P.filter (fun p : ℕ => r * (p : ℝ) ≤ N) ⊆ Nat.primesLE ⌊N / r⌋₊ := by
      intro p hp
      obtain ⟨hpP, hpN⟩ := Finset.mem_filter.mp hp
      apply Nat.mem_primesLE.mpr
      refine ⟨?_, (hP p hpP).1⟩
      apply Nat.le_floor
      exact (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hpN)
    have hcard : ((P.filter (fun p : ℕ => r * (p : ℝ) ≤ N)).card : ℝ) ≤
        Nat.primeCounting ⌊N / r⌋₊ := by
      have hc := Finset.card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at hc
      exact_mod_cast hc
    have hlog : Real.log y ≤ Real.log (N / r) :=
      Real.log_le_log (lt_trans zero_lt_one hy) ht
    calc
      _ ≤ (Nat.primeCounting ⌊N / r⌋₊ : ℝ) := hcard
      _ ≤ C * (N / r) / Real.log (N / r) := hcount _ ht
      _ ≤ C * (N / r) / Real.log y :=
        div_le_div_of_nonneg_left (mul_nonneg hC (div_nonneg hN hr.le)) hlogy hlog
      _ = _ := by ring
  · have hemp : P.filter (fun p : ℕ => r * (p : ℝ) ≤ N) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpP, hpN⟩ := Finset.mem_filter.mp hp
      have hpupper : (p : ℝ) ≤ N / r :=
        (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hpN)
      exact ht ((hP p hpP).2.le.trans hpupper)
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

private theorem primeTupleCount_le_fibers (P : Finset ℕ) (h : ℕ) (N : ℝ) :
    (primeTupleCount P (h + 1) N : ℝ) ≤
      ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        ((P.filter (fun p : ℕ => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)).card : ℝ) := by
  classical
  let A : Finset (Fin (h + 1) → ℕ) := (Fintype.piFinset fun _ : Fin (h + 1) => P).filter
    (fun f : Fin (h + 1) → ℕ => (∏ i, (f i : ℝ)) ≤ N)
  let B : Finset ((Fin h → ℕ) × ℕ) :=
    ((Fintype.piFinset fun _ : Fin h => P).product P).filter
      (fun fp : (Fin h → ℕ) × ℕ => (∏ i, (fp.1 i : ℝ)) * (fp.2 : ℝ) ≤ N)
  have hmap : Set.MapsTo (fun f : Fin (h + 1) → ℕ => (Fin.tail f, f 0)) A B := by
    intro f hf
    obtain ⟨hfP, hfN⟩ := Finset.mem_filter.mp hf
    have hall := Fintype.mem_piFinset.mp hfP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hall i.succ), hall 0⟩, ?_⟩
    change (∏ i : Fin h, (f i.succ : ℝ)) * (f 0 : ℝ) ≤ N
    have hprod := Fin.prod_univ_succ (fun i : Fin (h + 1) => (f i : ℝ))
    rw [hprod] at hfN
    simpa only [mul_comm] using hfN
  have hinj : (↑A : Set (Fin (h + 1) → ℕ)).InjOn
      (fun f => (Fin.tail f, f 0)) := by
    intro f hf g hg heq
    have htail := congrArg Prod.fst heq
    have hzero := congrArg Prod.snd heq
    ext i
    exact Fin.cases hzero (fun j => congrFun htail j) i
  have hc : (A.card : ℝ) ≤ B.card := by
    exact Nat.cast_le.mpr (Finset.card_le_card_of_injOn _ hmap hinj)
  calc
    _ = (A.card : ℝ) := rfl
    _ ≤ (B.card : ℝ) := hc
    _ = _ := card_filter_product_real (Fintype.piFinset fun _ : Fin h => P) P
      (fun (f : Fin h → ℕ) (p : ℕ) => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)

/-- The ordered tuple bound used for the floor error. It is valid without
distinctness restrictions on the prime entries. -/
theorem primeTupleCount_bound {P : Finset ℕ} {C y N : ℝ} (h : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ y < (p : ℝ)) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hcount : PrimeCountingUpperBound C y) :
    (primeTupleCount P (h + 1) N : ℝ) ≤
      (C * N / Real.log y) * (∑ p ∈ P, 1 / (p : ℝ)) ^ h := by
  classical
  calc
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        ((P.filter (fun p : ℕ => (∏ i, (f i : ℝ)) * (p : ℝ) ≤ N)).card : ℝ) :=
      primeTupleCount_le_fibers P h N
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin h => P),
        (C * N / Real.log y) * (1 / ∏ i, (f i : ℝ)) := by
      apply Finset.sum_le_sum
      intro f hf
      apply prime_product_fiber_bound hP hC hy hN _ hcount
      apply Finset.prod_pos
      intro i _
      exact lt_trans (lt_trans zero_lt_one hy)
        (hP (f i) (Fintype.mem_piFinset.mp hf i)).2
    _ = (C * N / Real.log y) * (∑ p ∈ P, 1 / (p : ℝ)) ^ h := by
      rw [← Finset.mul_sum, Finset.sum_pow']
      congr 1
      apply Finset.sum_congr rfl
      intro f _
      simp only [one_div, Finset.prod_inv_distrib]

theorem largePrimeTupleCount_bound {C y N : ℝ} (h : ℕ) (hC : 0 ≤ C)
    (hy : 1 < y) (hN : 0 ≤ N) (hcount : PrimeCountingUpperBound C y) :
    (primeTupleCount (largePrimeSet N y) (h + 1) N : ℝ) ≤
      (C * N / Real.log y) * (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) ^ h := by
  apply primeTupleCount_bound h _ hC hy hN hcount
  intro p hp
  obtain ⟨hpP, hpy⟩ := Finset.mem_filter.mp hp
  exact ⟨(Nat.mem_primesLE.mp hpP).2, hpy⟩

/-- For `y=N^c`, the tuple count is `o(N)` once the reciprocal-prime sum
is bounded. The explicit Chebyshev hypothesis is not discharged here. -/
theorem largePrimeTupleCount_density_tendsto_zero (h : ℕ) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hcount : ∀ᶠ N : ℝ in atTop, PrimeCountingUpperBound C (N ^ c))
    (hrecip : ∀ᶠ N : ℝ in atTop,
      (∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ)) ≤ K) :
    Tendsto (fun N : ℝ =>
      (primeTupleCount (largePrimeSet N (N ^ c)) (h + 1) N : ℝ) / N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℝ => Real.log (N ^ c)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hc)
  have hlim : Tendsto (fun N : ℝ => C * K ^ h / Real.log (N ^ c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · filter_upwards [hcount, hrecip, eventually_gt_atTop (1 : ℝ)] with N hCN hKN hN
    have hN0 : 0 < N := lt_trans zero_lt_one hN
    have hy : 1 < N ^ c := Real.one_lt_rpow hN hc
    have hlogpos : 0 < Real.log (N ^ c) := Real.log_pos hy
    have hsum0 : 0 ≤ ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ) := by
      apply Finset.sum_nonneg
      intro p hp
      positivity
    have hpowers := pow_le_pow_left₀ hsum0 hKN h
    have hbound := (largePrimeTupleCount_bound h hC hy hN0.le hCN).trans
      (mul_le_mul_of_nonneg_left hpowers (by positivity))
    calc
      _ ≤ ((C * N / Real.log (N ^ c)) * K ^ h) / N :=
        div_le_div_of_nonneg_right hbound hN0.le
      _ = C * K ^ h / Real.log (N ^ c) := by field_simp

end JointDickman

end OAI
