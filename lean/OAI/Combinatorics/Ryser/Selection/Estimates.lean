import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

theorem sum_le_card_mul_add_bad_card_mul {ι : Type*} (T : Finset ι)
    (bad : ι → Prop) [DecidablePred bad] (z : ι → ℝ) (threshold cap : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hregular : ∀ e ∈ T, ¬bad e → z e ≤ threshold)
    (hexception : ∀ e ∈ T, bad e → z e ≤ cap) :
    (∑ e ∈ T, z e) ≤ (T.card : ℝ) * threshold + ((T.filter bad).card : ℝ) * cap := by
  calc
    (∑ e ∈ T, z e) ≤ ∑ e ∈ T, (threshold + if bad e then cap else 0) := by
      apply Finset.sum_le_sum
      intro e he
      by_cases hb : bad e
      · simp only [ite_eq_left hb]
        linarith [hexception e he hb]
      · simpa only [ite_eq_right hb, add_zero] using hregular e he hb
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem mass_after_chunk_ge {ι : Type*} (T : Finset ι)
    (bad : ι → Prop) [DecidablePred bad] (z : ι → ℝ)
    (M M' m q C α γ : ℝ)
    (hM : 0 ≤ M) (hm : 0 ≤ m) (hq : 0 < q) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hhalf : C * α = 1 / 2)
    (hsize : (T.card : ℝ) ≤ α * q)
    (hbad : ((T.filter bad).card : ℝ) ≤ 2 * γ * q)
    (hregular : ∀ e ∈ T, ¬bad e → z e ≤ C * M / q + γ * m * q)
    (hexception : ∀ e ∈ T, bad e → z e ≤ C * m * q)
    (hloss : M - (∑ e ∈ T, z e) ≤ M') :
    M / 2 - (α + 2 * C) * γ * (m * q ^ 2) ≤ M' := by
  have hthreshold : 0 ≤ C * M / q + γ * m * q :=
    add_nonneg (div_nonneg (mul_nonneg hC hM) hq.le)
      (mul_nonneg (mul_nonneg hγ hm) hq.le)
  have hcap : 0 ≤ C * m * q := mul_nonneg (mul_nonneg hC hm) hq.le
  have hsum := sum_le_card_mul_add_bad_card_mul T bad z
    (C * M / q + γ * m * q) (C * m * q) hthreshold hregular hexception
  have htotal : (∑ e ∈ T, z e) ≤
      (α * q) * (C * M / q + γ * m * q) + (2 * γ * q) * (C * m * q) :=
    hsum.trans (add_le_add (mul_le_mul_of_nonneg_right hsize hthreshold)
      (mul_le_mul_of_nonneg_right hbad hcap))
  have heq : (α * q) * (C * M / q + γ * m * q) +
      (2 * γ * q) * (C * m * q) =
      (C * α) * M + (α + 2 * C) * γ * (m * q ^ 2) := by
    field_simp [hq.ne']
    ring
  rw [heq, hhalf] at htotal
  linarith

theorem mass_ge_geometric_sub_error (mass : ℕ → ℝ) (scale err : ℝ) (J : ℕ)
    (hscale : 0 ≤ scale) (herr : 0 ≤ err) (hstart : scale ≤ mass 0)
    (hstep : ∀ j < J, mass j / 2 - err * scale ≤ mass (j + 1)) :
    scale * (1 / 2 : ℝ) ^ J - 2 * err * scale ≤ mass J := by
  have hall : ∀ j ≤ J, scale * (1 / 2 : ℝ) ^ j - 2 * err * scale ≤ mass j := by
    intro j
    induction j with
    | zero =>
        intro _
        simp only [pow_zero, mul_one]
        nlinarith [mul_nonneg herr hscale]
    | succ j ih =>
        intro hj
        have hprev := ih (Nat.le_trans (Nat.le_succ j) hj)
        have hnext := hstep j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj)
        rw [pow_succ]
        nlinarith
  exact hall J le_rfl

theorem mass_after_chunks_ge_density (mass : ℕ → ℝ) (scale err : ℝ) (J J0 : ℕ)
    (hscale : 0 ≤ scale) (herr : 0 ≤ err) (hstart : scale ≤ mass 0)
    (hstep : ∀ j < J, mass j / 2 - err * scale ≤ mass (j + 1))
    (hJ : J ≤ J0) (hbudget : 2 * err ≤ (1 / 2 : ℝ) ^ (J0 + 1)) :
    (1 / 2 : ℝ) ^ (J0 + 1) * scale ≤ mass J := by
  have hbase := mass_ge_geometric_sub_error mass scale err J hscale herr hstart hstep
  have hpow : (1 / 2 : ℝ) ^ J0 ≤ (1 / 2 : ℝ) ^ J :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
  have hpowmul := mul_le_mul_of_nonneg_left hpow hscale
  have hbudgetmul := mul_le_mul_of_nonneg_right hbudget hscale
  calc
    (1 / 2 : ℝ) ^ (J0 + 1) * scale =
        scale * (1 / 2 : ℝ) ^ J0 - (1 / 2 : ℝ) ^ (J0 + 1) * scale := by
      rw [pow_succ]
      ring
    _ ≤ scale * (1 / 2 : ℝ) ^ J0 - 2 * err * scale := by linarith
    _ ≤ scale * (1 / 2 : ℝ) ^ J - 2 * err * scale :=
      sub_le_sub_right hpowmul _
    _ ≤ mass J := hbase

theorem unused_weight_ge {ι : Type*} (I : Finset ι) (p : ι → ℝ)
    (t : ι → ℕ) (K : ℕ) (δ m : ℝ)
    (hp : ∀ i ∈ I, p i ≤ 1) (ht : ∀ i ∈ I, t i ≤ K)
    (hdensity : δ * m ≤ ∑ i ∈ I, p i)
    (hcount : (∑ i ∈ I, (t i : ℝ)) ≤ 2 * m) :
    ((K : ℝ) * δ - 2) * m ≤ ∑ i ∈ I, ((K - t i : ℕ) : ℝ) * p i := by
  have hexposed : (∑ i ∈ I, (t i : ℝ) * p i) ≤ ∑ i ∈ I, (t i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp i hi) (Nat.cast_nonneg (t i))
  have hdense := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  have hidentity : (∑ i ∈ I, ((K - t i : ℕ) : ℝ) * p i) =
      (K : ℝ) * (∑ i ∈ I, p i) - ∑ i ∈ I, (t i : ℝ) * p i := by
    calc
      _ = ∑ i ∈ I, ((K : ℝ) * p i - (t i : ℝ) * p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.cast_sub (ht i hi), sub_mul]
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hidentity]
  nlinarith

theorem prod_one_sub_pow_le_exp_neg_sum {ι : Type*} (I : Finset ι)
    (p : ι → ℝ) (k : ι → ℕ) (hp : ∀ i ∈ I, p i ≤ 1) :
    (∏ i ∈ I, (1 - p i) ^ k i) ≤ Real.exp (-(∑ i ∈ I, (k i : ℝ) * p i)) := by
  calc
    (∏ i ∈ I, (1 - p i) ^ k i) ≤ ∏ i ∈ I, Real.exp (-p i) ^ k i := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact pow_nonneg (sub_nonneg.mpr (hp i hi)) _
      · intro i hi
        exact pow_le_pow_left₀ (sub_nonneg.mpr (hp i hi)) (Real.one_sub_le_exp_neg (p i)) _
    _ = ∏ i ∈ I, Real.exp (-((k i : ℝ) * p i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.exp_nat_mul, mul_neg]
    _ = Real.exp (∑ i ∈ I, -((k i : ℝ) * p i)) := (Real.exp_sum I _).symm
    _ = Real.exp (-(∑ i ∈ I, (k i : ℝ) * p i)) := by rw [Finset.sum_neg_distrib]

theorem unused_failure_product_le {ι : Type*} (I : Finset ι) (p : ι → ℝ)
    (t : ι → ℕ) (K : ℕ) (δ m : ℝ)
    (hp : ∀ i ∈ I, p i ≤ 1) (ht : ∀ i ∈ I, t i ≤ K)
    (hdensity : δ * m ≤ ∑ i ∈ I, p i)
    (hcount : (∑ i ∈ I, (t i : ℝ)) ≤ 2 * m) :
    (∏ i ∈ I, (1 - p i) ^ (K - t i)) ≤ Real.exp (-(((K : ℝ) * δ - 2) * m)) := by
  refine (prod_one_sub_pow_le_exp_neg_sum I p (fun i => K - t i) hp).trans ?_
  exact Real.exp_le_exp.mpr (neg_le_neg (unused_weight_ge I p t K δ m hp ht hdensity hcount))

end RyserCoveringCounterexample.Selection

end OAI
