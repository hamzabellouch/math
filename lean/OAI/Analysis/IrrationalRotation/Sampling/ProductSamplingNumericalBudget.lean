import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingPhaseScale
import OAI.Analysis.IrrationalRotation.Analysis.ScalarKernelMomentNumerics

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments

theorem pair_budget_of_power_ten {m : ℝ} (hm : 200 ≤ m) :
    (29 / m^80) * (16 * m^10)^2 ≤ m^(-50 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hsmall : (7424 : ℝ) ≤ m^2 := by nlinarith
  have hsize : (7424 : ℝ) ≤ m^10 := hsmall.trans
    (pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 10))
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hm0 80)]
  have hpow : m^(-50 : ℝ) * m^80 = m^30 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm0]
    norm_num
  rw [hpow]
  calc
    29 * (16 * m^10)^2 = 7424 * m^20 := by ring
    _ ≤ m^10 * m^20 := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = m^30 := by ring

theorem cross_budget_of_horizon {m N₀ n : ℝ} (hm : 200 ≤ m)
    (hN : N₀ ≤ m^2)
    (hn : m^((7 / 10 : ℝ) * m) / 2 ≤ n) :
    4 * N₀ / n ≤ m^(-50 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hQ : 0 < m^((7 / 10 : ℝ) * m) := Real.rpow_pos_of_pos hm0 _
  have hpow : m^(140 : ℝ) ≤ m^((7 / 10 : ℝ) * m) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hgap : (8 : ℝ) ≤ m^(88 : ℝ) := by
    calc
      (8 : ℝ) ≤ m := by linarith
      _ = m^(1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ m^(88 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  calc
    4 * N₀ / n ≤ 4 * m^2 / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num))
        ((div_pos hQ (by norm_num)).trans_le hn).le
    _ ≤ 4 * m^2 / (m^((7 / 10 : ℝ) * m) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hQ (by norm_num)) hn
    _ = 8 * (m^(2 : ℝ) / m^((7 / 10 : ℝ) * m)) := by rw [Real.rpow_two]; ring
    _ ≤ 8 * (m^(2 : ℝ) / m^(140 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hm0 _) hpow
    _ = 8 * m^(-138 : ℝ) := by rw [← Real.rpow_sub hm0]; norm_num
    _ ≤ m^(88 : ℝ) * m^(-138 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hm0.le _)
    _ = m^(-50 : ℝ) := by rw [← Real.rpow_add hm0]; norm_num

theorem averaged_square_budget {m : ℕ} (hm : 200 ≤ m) :
    1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      1 + 4 * (m : ℝ)^(-6 / 5 : ℝ) := by
  simpa only [neg_div] using add_le_add (le_rfl : (1 : ℝ) ≤ 1)
    (ScalarSampling.kernel_average_square_remainder_le hm)

theorem product_sampling_nonempty {p : ProductScaleData} (hp : ProductScaleLaws p)
    {j : ℕ} {powers : Finset ℕ} (hs : ProductSamplingPowersAt p j powers) :
    powers.Nonempty := by
  have hpos : 0 < (p.m j : ℝ)^((69 / 100 : ℝ) * p.m j) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.m_pos j) _
  exact Finset.card_pos.mp (by exact_mod_cast hpos.trans_le hs.cardinality)

theorem expected_average_error_le_source_scale {κ : Type*} [Fintype κ]
    {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
    (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
    (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
    (u : κ → ℝ → ℝ → ℝ) (C : κ → ℝ)
    (hu : ∀ i, Measurable (Function.uncurry (u i)))
    (hbound : ∀ i s t, |u i s t| ≤ C i)
    (hzero : ∀ i s t, 0 ≤ u i s t)
    (hmean : ∀ i s, mean (u i) s ≤ 2)
    (hBV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → BoundedVariationOn (u i s) (Icc (0 : ℝ) 1))
    (hV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → realBVSize (u i s) ≤ 16 * (p.m j : ℝ)^10)
    (hbase : ∀ i, (∫ s, (mean (u i) s)^2 ∂unitInterval) ≤
      1 + ((p.m j : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (p.m j : ℝ)^(-(3 / 5 : ℝ)))^2)
    {D : ℝ}
    (hsquare : ∀ i, (∫ s, ∫ t, (u i s t)^2 ∂unitInterval ∂unitInterval) ≤ D) :
    (∫ a, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * a i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (2 * D)^Fintype.card κ / (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
          (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
            (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1)) := by
  apply expected_average_error_le hm N₀ hN (p.N j) powers
    (product_sampling_nonempty hp hs) hs.positive
  · intro n hn i
    exact coordinate_scale_le_power hp hm hs (hNle i) hn
  · intro n hn n' hn' hne i
    exact samplingPair_of_product_powers hp hs (hN i) (hNle i) hn hn' hne
  · exact hu
  · exact hbound
  · exact hzero
  · exact hmean
  · positivity
  · positivity
  · exact hBV
  · exact hV
  · intro i
    exact (hbase i).trans (averaged_square_budget hm)
  · exact hsquare
  · exact pair_budget_of_power_ten (by exact_mod_cast hm)
  · intro n hn i
    exact cross_budget_of_horizon (by exact_mod_cast hm)
      ((hNle i).trans (hp.N_le_square j)) (hs.range n hn).1

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
