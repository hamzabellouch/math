import OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectMean
import OAI.NumberTheory.TwoPoint.Bounds.CRTComparison

namespace OAI

/-! The ordinary mean of the finite prime-defect majorant is computed by
CRT modulo the squared primes. Only the finite interval boundary remains. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma uniformAverage_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] (F : ∀ i, β i → ℝ) :
    uniformAverage (fun r : ∀ i, β i => ∏ i, F i (r i)) =
      ∏ i, uniformAverage (F i) := by
  unfold uniformAverage
  rw [Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum, prod_div_distrib]

lemma primeDefectMajorant_crt_bound {f : ℕ → ℂ}
    (hfm : Multiplicative f) (hf1 : f 1 = 1) (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ) ≤
      (∏ p ∈ P, (1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))) +
        (∏ p ∈ P, (p : ℝ) ^ 2) / N := by
  let s : P → ℕ := fun p => p.val ^ 2
  let : ∀ p : P, NeZero (s p) := fun p => ⟨pow_ne_zero _ (hP p.val p.property).ne_zero⟩
  let F : (∀ p : P, ZMod (s p)) → ℝ := fun r =>
    ∏ p : P, primeDefectLocal f p.val (r p).val
  have hcop : Pairwise (fun p q : P => (s p).Coprime (s q)) := by
    intro p q hpq
    have hp : p.val.Coprime q.val := (Nat.coprime_primes
      (hP p.val p.property) (hP q.val q.property)).mpr (by
        intro h
        exact hpq (Subtype.ext h))
    exact (hp.pow_left 2).pow_right 2
  have hF : ∀ r, |F r| ≤ 1 := by
    intro r
    have hn : 0 ≤ F r := prod_nonneg (fun p _ => primeDefectLocal_nonneg f _ _)
    rw [abs_of_nonneg hn]
    exact prod_le_one₀ (fun p _ => primeDefectLocal_nonneg f _ _)
      (fun p _ => primeDefectLocal_le_one hf (hP p.val p.property) _)
  have hmodel : uniformAverage F =
      ∏ p ∈ P, (1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)) := by
    change uniformAverage (fun r : ∀ p : P, ZMod (s p) =>
      ∏ p : P, primeDefectLocal f p.val (r p).val) = _
    rw [uniformAverage_pi_product (fun p : P => ZMod (s p))
      (fun p r => primeDefectLocal f p.val r.val)]
    calc
      _ = ∏ p : P, (1 - (1 - ‖f p.val‖) *
          (1 / (p.val : ℝ) - 1 / (p.val : ℝ) ^ 2)) := by
        apply prod_congr rfl
        intro p _
        exact primeDefectLocal_average f (hP p.val p.property)
      _ = _ := prod_coe_sort P (fun p : ℕ =>
        1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))
  have hpoint (n : ℕ) :
      F (ZMod.prodEquivPi s hcop (n : ZMod (∏ p : P, s p))) =
        primeDefectMajorant f P n := by
    have he : ZMod.prodEquivPi s hcop (n : ZMod (∏ p : P, s p)) =
        fun p => (n : ZMod (s p)) := by
      funext p
      simp only [ZMod.prodEquivPi_apply]
      exact ZMod.cast_natCast (dvd_prod_of_mem s (mem_univ p)) n
    rw [he]
    change (∏ p : P, primeDefectLocal f p.val (n : ZMod (s p)).val) = _
    simp only [ZMod.val_natCast, s, primeDefectLocal_mod]
    exact prod_coe_sort P (fun p => primeDefectLocal f p n)
  have he := crt_observable_difference s hcop (1 : ZMod (∏ p : P, s p)) N hN F hF
  have hreal : uniformAverage (fun j : Fin N =>
      F (ZMod.prodEquivPi s hcop (1 + (j.val : ZMod (∏ p : P, s p))))) =
      (∑ n ∈ range N, primeDefectMajorant f P (n + 1)) / (N : ℝ) := by
    unfold uniformAverage
    rw [Fintype.card_fin, ← Fin.sum_univ_eq_sum_range]
    congr 1
    apply sum_congr rfl
    intro j _
    change F (ZMod.prodEquivPi s hcop (1 + (j.val : ZMod (∏ p : P, s p)))) = _
    rw [show (1 : ZMod (∏ p : P, s p)) + (j.val : ZMod (∏ p : P, s p)) =
      ((j.val + 1 : ℕ) : ZMod (∏ p : P, s p)) by push_cast; ring, hpoint]
  rw [hreal, hmodel] at he
  have hprod : ((∏ p : P, s p : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) ^ 2 := by
    simp only [Nat.cast_prod, s, Nat.cast_pow]
    exact prod_coe_sort P (fun p : ℕ => (p : ℝ) ^ 2)
  rw [hprod] at he
  apply (div_le_div_of_nonneg_right
    (sum_le_sum (fun n _ => norm_le_primeDefectMajorant hfm hf1 hf P hP (n + 1) (by omega)))
    (Nat.cast_nonneg N)).trans
  have hb := le_trans (le_abs_self _) he
  linarith

end TwoPointCorrelations

end OAI
