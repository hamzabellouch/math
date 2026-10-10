import OAI.Analysis.IrrationalRotation.Sampling.SamplingErrorSummability
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingEstimates
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Model.ProductScaleSampling

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductSampling

theorem eventually_const_log_le_rpow (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ m : ℝ in atTop, c * Real.log m ≤ m ^ r := by
  have h := ((isLittleO_log_rpow_atTop hr).const_mul_left c).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with m hm hm0
  calc
    c * Real.log m ≤ ‖c * Real.log m‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (c * Real.log m)
    _ ≤ m ^ r := by simpa only [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hm0 r)] using hm

theorem diagonal_product_le_source_power {m c : ℝ} {d : ℕ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hlog : c * Real.log m ≤ m ^ (1 / 25 : ℝ))
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d ≤
      m ^ ((13 / 20 : ℝ) * m) := by
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hbase : c * m ^ (3 / 5 : ℝ) * Real.log m ≤ m ^ (16 / 25 : ℝ) := by
    calc
      c * m ^ (3 / 5 : ℝ) * Real.log m = m ^ (3 / 5 : ℝ) * (c * Real.log m) := by ring
      _ ≤ m ^ (3 / 5 : ℝ) * m ^ (1 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hm0 _)
      _ = m ^ (16 / 25 : ℝ) := by rw [← Real.rpow_add hmpos]; norm_num
  have hnonneg : 0 ≤ c * m ^ (3 / 5 : ℝ) * Real.log m :=
    mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hm0 _)) (Real.log_nonneg hm)
  calc
    (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d ≤ (m ^ (16 / 25 : ℝ)) ^ d :=
      pow_le_pow_left₀ hnonneg hbase d
    _ = m ^ ((16 / 25 : ℝ) * (d : ℝ)) := (Real.rpow_mul_natCast hm0 _ _).symm
    _ ≤ m ^ ((13 / 20 : ℝ) * m) := by
      apply Real.rpow_le_rpow_of_exponent_le hm
      nlinarith

theorem diagonal_sampling_ratio_le {m c P : ℝ} {d : ℕ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hlog : c * Real.log m ≤ m ^ (1 / 25 : ℝ))
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hP : m ^ ((69 / 100 : ℝ) * m) ≤ P) :
    (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤ m ^ (-m / 25) := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hden : 0 < m ^ ((69 / 100 : ℝ) * m) := Real.rpow_pos_of_pos hmpos _
  have hPpos : 0 < P := hden.trans_le hP
  calc
    (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤
        m ^ ((13 / 20 : ℝ) * m) / P :=
      div_le_div_of_nonneg_right (diagonal_product_le_source_power hm hc hlog hd) hPpos.le
    _ ≤ m ^ ((13 / 20 : ℝ) * m) / m ^ ((69 / 100 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _) hden hP
    _ = m ^ (-m / 25) := by rw [← Real.rpow_sub hmpos]; congr 1; ring

theorem eventually_diagonal_sampling_ratio_le (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ d : ℕ, ∀ P : ℝ,
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤ m ^ (-m / 25) := by
  filter_upwards [eventually_const_log_le_rpow c (by norm_num : (0 : ℝ) < 1 / 25),
    eventually_ge_atTop (1 : ℝ)] with m hlog hm
  intro d P hd hP
  exact diagonal_sampling_ratio_le hm hc hlog hd hP

theorem dimension_error_le {m C : ℝ} {d : ℕ} (hm : 0 < m) (hC : 0 ≤ C)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    C * (d : ℝ) * m ^ (-40 : ℝ) ≤
      ((101 / 100 : ℝ) * C) * m ^ (-39 : ℝ) := by
  calc
    C * (d : ℝ) * m ^ (-40 : ℝ) ≤
        C * ((101 / 100 : ℝ) * m) * m ^ (-40 : ℝ) := by gcongr
    _ = ((101 / 100 : ℝ) * C) * (m ^ (1 : ℝ) * m ^ (-40 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = ((101 / 100 : ℝ) * C) * m ^ (-39 : ℝ) := by
      rw [← Real.rpow_add hm]; norm_num

theorem eventually_sampling_error_le (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    ∀ᶠ m : ℝ in atTop, ∀ d : ℕ, ∀ P : ℝ,
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      C * (d : ℝ) * m ^ (-40 : ℝ) +
          (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤
        ((101 / 100 : ℝ) * C) * m ^ (-39 : ℝ) + m ^ (-m / 25) := by
  filter_upwards [eventually_diagonal_sampling_ratio_le c hc,
    eventually_ge_atTop (1 : ℝ)] with m hdiag hm d P hd hP
  exact add_le_add (dimension_error_le (zero_lt_one.trans_le hm) hC hd)
    (hdiag d P hd hP)

theorem sampling_moment_majorant_summable
    {m : ℕ → ℝ} {d : ℕ → ℕ} {P : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n)
    (hd : ∀ᶠ n in atTop, (d n : ℝ) ≤ (101 / 100 : ℝ) * m n)
    (hP : ∀ᶠ n in atTop, m n ^ ((69 / 100 : ℝ) * m n) ≤ P n)
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    Summable (fun n => C * (d n : ℝ) * m n ^ (-40 : ℝ) +
      (c * m n ^ (3 / 5 : ℝ) * Real.log (m n)) ^ d n / P n) := by
  have hmTop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hb := hmTop.eventually (eventually_sampling_error_le c C hc hC)
  apply (sampling_error_majorant_summable hm ((101 / 100 : ℝ) * C)).of_norm_bounded_eventually_nat
  filter_upwards [hb, hd, hP, hmTop.eventually_ge_atTop 1] with n hn hdn hPn hmn
  have hmpos : 0 < m n := zero_lt_one.trans_le hmn
  have hPpos : 0 < P n := (Real.rpow_pos_of_pos hmpos _).trans_le hPn
  have hnonneg : 0 ≤ C * (d n : ℝ) * m n ^ (-40 : ℝ) +
      (c * m n ^ (3 / 5 : ℝ) * Real.log (m n)) ^ d n / P n := by
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Real.rpow_nonneg hmpos.le _)
    · apply div_nonneg _ hPpos.le
      apply pow_nonneg
      exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hmpos.le _)) (Real.log_nonneg hmn)
  rw [Real.norm_of_nonneg hnonneg]
  exact hn (d n) (P n) hdn hPn

theorem growing_moment_power_le_exp {m c : ℝ} {d : ℕ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    (1 + c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)) ^ (d - 1) ≤
      Real.exp ((101 / 50 : ℝ) * c) := by
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  let δ : ℝ := c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htotal : (d : ℝ) * δ ≤ (101 / 50 : ℝ) * c := by
    calc
      (d : ℝ) * δ ≤ ((101 / 100 : ℝ) * m) * δ :=
        mul_le_mul_of_nonneg_right hd hδ
      _ = ((101 / 100 : ℝ) * c) *
          (m * m ^ (-6 / 5 : ℝ) + m * m ^ (-50 : ℝ)) := by dsimp [δ]; ring
      _ ≤ ((101 / 100 : ℝ) * c) * (1 + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_rpow_le_one hm (by norm_num))
          (mul_rpow_le_one hm (by norm_num))
      _ = (101 / 50 : ℝ) * c := by ring
  have heq : 1 + c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ) = 1 + δ := by
    dsimp [δ]; ring
  rw [heq]
  calc
    (1 + δ) ^ (d - 1) ≤ (1 + δ) ^ d :=
      pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
    _ ≤ Real.exp δ ^ d := by
      apply pow_le_pow_left₀ (by linarith)
      simpa only [add_comm] using Real.add_one_le_exp δ
    _ = Real.exp ((d : ℝ) * δ) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((101 / 50 : ℝ) * c) := Real.exp_le_exp.mpr htotal

theorem exact_moment_error_le {m c : ℝ} {d : ℕ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
      (1 + c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
      ((303 / 100 : ℝ) * c * Real.exp ((101 / 50 : ℝ) * c)) * m ^ (-39 : ℝ) := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hp := growing_moment_power_le_exp hm hc hd
  have hr : m ^ (-50 : ℝ) ≤ m ^ (-40 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have he := dimension_error_le hmpos
    (show 0 ≤ 3 * c * Real.exp ((101 / 50 : ℝ) * c) by positivity) hd
  calc
    3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
        (1 + c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
        3 * ((d : ℝ) * (c * m ^ (-40 : ℝ)) * Real.exp ((101 / 50 : ℝ) * c)) := by
      gcongr
    _ = (3 * c * Real.exp ((101 / 50 : ℝ) * c)) * (d : ℝ) * m ^ (-40 : ℝ) := by ring
    _ ≤ ((101 / 100 : ℝ) * (3 * c * Real.exp ((101 / 50 : ℝ) * c))) *
        m ^ (-39 : ℝ) := he
    _ = ((303 / 100 : ℝ) * c * Real.exp ((101 / 50 : ℝ) * c)) * m ^ (-39 : ℝ) := by ring

theorem eventually_exact_second_moment_le (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ d : ℕ, ∀ P : ℝ,
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P +
          3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
            (1 + c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
        ((303 / 100 : ℝ) * c * Real.exp ((101 / 50 : ℝ) * c)) * m ^ (-39 : ℝ) +
          m ^ (-m / 25) := by
  filter_upwards [eventually_diagonal_sampling_ratio_le c hc,
    eventually_ge_atTop (1 : ℝ)] with m hdiag hm d P hd hP
  exact (add_le_add (hdiag d P hd hP) (exact_moment_error_le hm hc hd)).trans_eq (add_comm _ _)

end Invariant233.ProductSampling

namespace Invariant233.ProductScaleLaws

theorem sampling_moment_majorant_summable {p : ProductScaleData}
    (hp : ProductScaleLaws p) {s : ℕ → Finset ℕ}
    (hs : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (s j))
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    Summable (fun j => C * (p.prefixCount (j + 1) : ℝ) * (p.m j : ℝ) ^ (-40 : ℝ) +
      (c * (p.m j : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m j)) ^ p.prefixCount (j + 1) /
        ((s j).card : ℝ)) := by
  apply ProductSampling.sampling_moment_majorant_summable
  · intro j
    exact_mod_cast hp.m_ge_pow_self j
  · exact Eventually.of_forall hp.prefix_count_succ_le
  · filter_upwards [hs] with j hj using hj.cardinality
  · exact hc
  · exact hC

end Invariant233.ProductScaleLaws

end OAI
