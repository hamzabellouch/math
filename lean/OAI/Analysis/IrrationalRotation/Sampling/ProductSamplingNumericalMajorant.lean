import OAI.Analysis.IrrationalRotation.Sampling.SamplingErrorSummability
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Model.ProductScaleSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.ProductSampling

theorem eventually_const_mul_log_le_rpow (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℝ in atTop, c * Real.log m ≤ m ^ δ := by
  have h := ((isLittleO_log_rpow_atTop hδ).const_mul_left c).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with m hm hm0
  have habs : |c * Real.log m| ≤ m ^ δ := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg hm0 δ)] using hm
  exact (le_abs_self _).trans habs

theorem diagonal_sampling_term_le
    {c m P : ℝ} {d : ℕ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hlog : c * Real.log m ≤ m ^ (1 / 25 : ℝ))
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hP : m ^ ((69 / 100 : ℝ) * m) ≤ P) :
    (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤ m ^ (-m / 25) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hn0 : 0 ≤ c * m ^ (3 / 5 : ℝ) * Real.log m := by
    exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hm0.le _)) (Real.log_nonneg hm)
  have hbase : c * m ^ (3 / 5 : ℝ) * Real.log m ≤ m ^ (16 / 25 : ℝ) := by
    calc
      c * m ^ (3 / 5 : ℝ) * Real.log m = m ^ (3 / 5 : ℝ) * (c * Real.log m) := by ring
      _ ≤ m ^ (3 / 5 : ℝ) * m ^ (1 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hm0.le _)
      _ = m ^ (16 / 25 : ℝ) := by rw [← Real.rpow_add hm0]; norm_num
  have hnum : (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d ≤
      m ^ ((13 / 20 : ℝ) * m) := by
    calc
      _ ≤ (m ^ (16 / 25 : ℝ)) ^ d := pow_le_pow_left₀ hn0 hbase d
      _ = m ^ ((16 / 25 : ℝ) * (d : ℝ)) := (Real.rpow_mul_natCast hm0.le _ _).symm
      _ ≤ m ^ ((13 / 20 : ℝ) * m) := by
        apply Real.rpow_le_rpow_of_exponent_le hm
        nlinarith
  have hP0 : 0 < m ^ ((69 / 100 : ℝ) * m) := Real.rpow_pos_of_pos hm0 _
  calc
    _ ≤ m ^ ((13 / 20 : ℝ) * m) / P := div_le_div_of_nonneg_right hnum (hP0.le.trans hP)
    _ ≤ m ^ ((13 / 20 : ℝ) * m) / m ^ ((69 / 100 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hm0.le _) hP0 hP
    _ = m ^ (-m / 25) := by
      rw [← Real.rpow_sub hm0]
      congr 1
      ring

theorem eventually_diagonal_sampling_term_le (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ (d : ℕ) (P : ℝ),
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤ m ^ (-m / 25) := by
  filter_upwards [eventually_const_mul_log_le_rpow c (by norm_num : (0 : ℝ) < 1 / 25),
    eventually_ge_atTop (1 : ℝ)] with m hlog hm
  exact fun d P hd hP => diagonal_sampling_term_le hc hm hlog hd hP

theorem sampling_product_factor_le_exp
    {c m : ℝ} {d : ℕ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    (1 + c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)) ^ (d - 1) ≤
      Real.exp (3 * c) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let β : ℝ := c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hsmall (r : ℝ) (hr : r ≤ -1) : m ^ r ≤ m⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hm hr
  have hβbound : β ≤ 2 * c * m⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left (hsmall (-(6 / 5 : ℝ)) (by norm_num)) hc
    have h2 := mul_le_mul_of_nonneg_left (hsmall (-50 : ℝ) (by norm_num)) hc
    dsimp [β]
    linarith
  have hdim : (d : ℝ) * β ≤ 3 * c := by
    calc
      (d : ℝ) * β ≤ ((101 / 100 : ℝ) * m) * (2 * c * m⁻¹) :=
        mul_le_mul hd hβbound hβ (by positivity)
      _ = (101 / 50 : ℝ) * c := by field_simp; ring
      _ ≤ 3 * c := by linarith
  have hdm : ((d - 1 : ℕ) : ℝ) * β ≤ 3 * c := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hβ) hdim
    exact_mod_cast Nat.sub_le d 1
  have hbase : 1 + β ≤ Real.exp β := by simpa only [add_comm] using Real.add_one_le_exp β
  rw [add_assoc]
  change (1 + β) ^ (d - 1) ≤ _
  calc
    (1 + β) ^ (d - 1) ≤ (Real.exp β) ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp (((d - 1 : ℕ) : ℝ) * β) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (3 * c) := Real.exp_le_exp.mpr hdm

theorem sampling_product_error_le
    {c m : ℝ} {d : ℕ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
      (1 + c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
      (4 * c * Real.exp (3 * c)) * m ^ (-39 : ℝ) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hfactor := sampling_product_factor_le_exp hc hm hd
  have hcancel : m * m ^ (-50 : ℝ) = m ^ (-49 : ℝ) := by
    calc
      m * m ^ (-50 : ℝ) = m ^ (1 : ℝ) * m ^ (-50 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ (-49 : ℝ) := by rw [← Real.rpow_add hm0]; norm_num
  have hdim : (d : ℝ) * m ^ (-50 : ℝ) ≤ (101 / 100 : ℝ) * m ^ (-39 : ℝ) := by
    calc
      (d : ℝ) * m ^ (-50 : ℝ) ≤ ((101 / 100 : ℝ) * m) * m ^ (-50 : ℝ) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hm0.le _)
      _ = (101 / 100 : ℝ) * m ^ (-49 : ℝ) := by rw [mul_assoc, hcancel]
      _ ≤ (101 / 100 : ℝ) * m ^ (-39 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  calc
    _ ≤ 3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) * Real.exp (3 * c)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (3 * c * Real.exp (3 * c)) * ((d : ℝ) * m ^ (-50 : ℝ)) := by ring
    _ ≤ (3 * c * Real.exp (3 * c)) * ((101 / 100 : ℝ) * m ^ (-39 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdim (by positivity)
    _ ≤ (4 * c * Real.exp (3 * c)) * m ^ (-39 : ℝ) := by
      nlinarith [mul_nonneg hc (mul_nonneg (Real.exp_pos (3 * c)).le
        (Real.rpow_nonneg hm0.le (-39 : ℝ)))]

theorem eventually_sampling_moment_majorant (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ (d : ℕ) (P : ℝ),
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P +
        3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
          (1 + c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
        (4 * c * Real.exp (3 * c)) * m ^ (-39 : ℝ) + m ^ (-m / 25) := by
  filter_upwards [eventually_diagonal_sampling_term_le c hc,
    eventually_ge_atTop (1 : ℝ)] with m hdiag hm
  intro d P hd hP
  have h1 := hdiag d P hd hP
  have h2 := sampling_product_error_le hc hm hd
  linarith

theorem summable_of_sampling_moment_bound
    {m e : ℕ → ℝ} (hm : ∀ n, (2 : ℝ) ^ n ≤ m n)
    (c : ℝ) (hc : 0 ≤ c) (d : ℕ → ℕ) (P : ℕ → ℝ)
    (hd : ∀ᶠ n in atTop, (d n : ℝ) ≤ (101 / 100 : ℝ) * m n)
    (hP : ∀ᶠ n in atTop, (m n) ^ ((69 / 100 : ℝ) * m n) ≤ P n)
    (he : ∀ n, 0 ≤ e n)
    (herror : ∀ᶠ n in atTop,
      e n ≤ (c * (m n) ^ (3 / 5 : ℝ) * Real.log (m n)) ^ (d n) / P n +
        3 * ((d n : ℝ) * (c * (m n) ^ (-50 : ℝ)) *
          (1 + c * (m n) ^ (-(6 / 5 : ℝ)) + c * (m n) ^ (-50 : ℝ)) ^ (d n - 1))) :
    Summable e := by
  have hmTop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hbound := hmTop.eventually (eventually_sampling_moment_majorant c hc)
  apply (sampling_error_majorant_summable hm (4 * c * Real.exp (3 * c))).of_norm_bounded_eventually_nat
  filter_upwards [hbound, hd, hP, herror] with n hn hdn hPn hen
  rw [Real.norm_of_nonneg (he n)]
  exact hen.trans (hn (d n) (P n) hdn hPn)

end Invariant233.ProductSampling

namespace Invariant233.ProductScaleLaws

theorem summable_sampling_error_of_moment_bound
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (s : ℕ → Finset ℕ)
    (hs : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (s n))
    (c : ℝ) (hc : 0 ≤ c) (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (herror : ∀ᶠ n in atTop,
      e n ≤ (c * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n)) ^
          (p.prefixCount (n + 1)) / ((s n).card : ℝ) +
        3 * ((p.prefixCount (n + 1) : ℝ) * (c * (p.m n : ℝ) ^ (-50 : ℝ)) *
          (1 + c * (p.m n : ℝ) ^ (-(6 / 5 : ℝ)) +
            c * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))) :
    Summable e := by
  apply ProductSampling.summable_of_sampling_moment_bound
    (m := fun n => (p.m n : ℝ)) (fun n => by exact_mod_cast hp.m_ge_pow_self n)
    c hc (fun n => p.prefixCount (n + 1)) (fun n => ((s n).card : ℝ))
    (Eventually.of_forall hp.prefix_count_succ_le) _ he herror
  exact hs.mono fun _ hn => hn.cardinality

end Invariant233.ProductScaleLaws

end

end OAI
