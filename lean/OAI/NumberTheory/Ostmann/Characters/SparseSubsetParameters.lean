import OAI.NumberTheory.Ostmann.Supply.TailSieveParameters

namespace OAI

/-! # Uniform product and reciprocal bounds for small sparse-prime subsets -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem primeProduct_le_exp_sum_log {ι : Type*} (T : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ T, 0 < p i) :
    ((∏ i ∈ T, p i : ℕ) : ℝ) = Real.exp (∑ i ∈ T, Real.log (p i)) := by
  rw [Nat.cast_prod, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (by exact_mod_cast hp i hi)).symm

theorem eventual_sparse_subset_parameters (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (p : Fin n → ℕ),
      (∀ i, p i ∈ logLogPrimeBand L) →
      ∀ T : Finset (Fin n), (T.card : ℝ) ≤ c * L →
      (∏ i ∈ T, p i) ≤ ⌊Real.exp (Real.exp L / 2)⌋₊ ∧
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16 := by
  have hsmall := eventual_small_subset_reciprocal (1 / 20) c (by norm_num) hc
  have hgrowth := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left c).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hsmall, hgrowth, eventually_ge_atTop (1 : ℝ)] with L hsmall hgrowth hL
  intro n p hp T hT
  have hLp : 0 < L := by linarith
  have hlin : c * L ≤ (1 / 2 : ℝ) * Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hLp.le),
      abs_of_pos (Real.exp_pos _)] using hgrowth
  have hsum : (∑ i ∈ T, Real.log (p i)) ≤ Real.exp L / 2 := by
    calc
      _ ≤ (T.card : ℝ) * Real.exp ((9 / 10 : ℝ) * L) := by
        have hh := Finset.sum_le_sum (s := T) (fun i _ => (logLogPrimeBand_mem (hp i)).2.2)
        simpa only [Finset.sum_const, nsmul_eq_mul] using hh
      _ ≤ (c * L) * Real.exp ((9 / 10 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hT (Real.exp_nonneg _)
      _ ≤ ((1 / 2 : ℝ) * Real.exp ((1 / 10 : ℝ) * L)) *
          Real.exp ((9 / 10 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        rw [show (1 / 10 : ℝ) * L + (9 / 10 : ℝ) * L = L by ring]
        ring
  refine ⟨Nat.le_floor ?_, ?_⟩
  · rw [primeProduct_le_exp_sum_log T p (fun i _ => (logLogPrimeBand_mem (hp i)).1.pos)]
    exact Real.exp_le_exp.mpr hsum
  · apply hsmall (T.image p)
    · have hcard : ((T.image p).card : ℝ) ≤ T.card := by
        exact_mod_cast Finset.card_image_le (s := T) (f := p)
      exact hcard.trans hT
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      have hprime := (logLogPrimeBand_mem (hp i)).1
      refine ⟨hprime.pos, ?_⟩
      have he := Real.add_one_le_exp ((1 / 20 : ℝ) * L)
      linarith [(logLogPrimeBand_mem (hp i)).2.1]

end Ostmann

end OAI
