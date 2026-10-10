import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousConvolutionWeights

namespace OAI

/-! # The low homogeneous energy is controlled by L² and the high energy

This is the elementary frequency splitting used for the compact interior
potential term. The indices are exactly 6-a and k from the manuscript.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- Plancherel with the manuscript's radian Fourier normalization. -/
theorem radianFourier_energy_zero (f : 𝓢(E, ℂ)) :
    homogeneousFrequencyEnergy 0 (radianFourierKernel f) =
      (2 * Real.pi) ^ (12 : ℕ) * homogeneousFrequencyEnergy 0 f := by
  have hp : 0 < 2 * Real.pi := by positivity
  change homogeneousFrequencyEnergy 0 (fun ξ => (𝓕 f : 𝓢(E, ℂ)) ((2 * Real.pi)⁻¹ • ξ)) = _
  rw [homogeneousFrequencyEnergy_dilation 0 _ (inv_pos.mpr hp)]
  have hF : homogeneousFrequencyEnergy 0 (𝓕 f : 𝓢(E, ℂ)) = homogeneousFrequencyEnergy 0 f := by
    simpa only [homogeneousFrequencyEnergy, mul_zero, Real.rpow_zero, one_mul] using
      SchwartzMap.integral_norm_sq_fourier f
  rw [hF]
  congr 1
  simp only [mul_zero, sub_zero]
  rw [Real.rpow_neg (inv_nonneg.mpr hp.le)]
  rw [Real.rpow_ofNat, inv_pow, inv_inv]

private theorem low_weight_interpolation (a k ε : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      x ^ (2 * (6 - a)) ≤ ε * x ^ (2 * k) + C := by
  let R := max 1 ε⁻¹
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  refine ⟨R ^ (2 * (6 - a)), Real.rpow_nonneg hRpos.le _, ?_⟩
  intro x hx
  by_cases hsmall : x ≤ R
  · exact (Real.rpow_le_rpow hx hsmall (by linarith)).trans
      (le_add_of_nonneg_left (mul_nonneg hε.le (Real.rpow_nonneg hx _)))
  · have hlarge : R ≤ x := (lt_of_not_ge hsmall).le
    have hx1 : 1 ≤ x := hR.trans hlarge
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hi : x⁻¹ ≤ ε := by
      have hR' : ε⁻¹ ≤ x := (le_max_right _ _).trans hlarge
      have hp : 1 ≤ ε * x := by
        simpa only [mul_inv_cancel₀ hε.ne'] using mul_le_mul_of_nonneg_left hR' hε.le
      exact (inv_le_iff_one_le_mul₀ hxpos).mpr hp
    calc
      x ^ (2 * (6 - a)) = x ^ (2 * k) * x ^ (2 * (6 - a) - 2 * k) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      _ ≤ x ^ (2 * k) * x ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (Real.rpow_nonneg hx _)
      _ ≤ x ^ (2 * k) * ε := by rw [Real.rpow_neg_one]; gcongr
      _ ≤ ε * x ^ (2 * k) + R ^ (2 * (6 - a)) := by
        nlinarith [Real.rpow_nonneg hRpos.le (2 * (6 - a))]

theorem homogeneousLowEnergy_interpolation (a k ε : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → ℂ,
      Integrable (fun ξ => ‖f ξ‖ ^ 2) →
      Integrable (fun ξ => ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2) →
      homogeneousFrequencyEnergy (6 - a) f ≤
        ε * homogeneousFrequencyEnergy k f + C * homogeneousFrequencyEnergy 0 f := by
  obtain ⟨C, hC, hweight⟩ := low_weight_interpolation a k ε ha ha1 hk hε
  refine ⟨C, hC, ?_⟩
  intro f h0 hh
  have hmajor := (hh.const_mul ε).add (h0.const_mul C)
  have hbound : ∀ ξ : E, ‖ξ‖ ^ (2 * (6 - a)) * ‖f ξ‖ ^ 2 ≤
      ε * (‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2) + C * ‖f ξ‖ ^ 2 := by
    intro ξ
    have h := mul_le_mul_of_nonneg_right (hweight ‖ξ‖ (norm_nonneg _)) (sq_nonneg ‖f ξ‖)
    nlinarith
  have hi := integral_mono_of_nonneg (ae_of_all _ (fun ξ =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg ‖f ξ‖)))
      hmajor (ae_of_all _ hbound)
  simpa only [Pi.add_apply, integral_add (hh.const_mul ε) (h0.const_mul C), integral_const_mul,
    homogeneousFrequencyEnergy, mul_zero, Real.rpow_zero, one_mul] using hi

theorem tendsto_homogeneousLowEnergy_of_L2 (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M)
    (f : ℕ → E → ℂ)
    (h0 : ∀ n, Integrable (fun ξ => ‖f n ξ‖ ^ 2))
    (hh : ∀ n, Integrable (fun ξ => ‖ξ‖ ^ (2 * k) * ‖f n ξ‖ ^ 2))
    (hhigh : ∀ n, homogeneousFrequencyEnergy k (f n) ≤ M)
    (hlow : Tendsto (fun n => homogeneousFrequencyEnergy 0 (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousFrequencyEnergy (6 - a) (f n)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro d hd
    exact Filter.Eventually.of_forall (fun n => hd.trans_le (integral_nonneg (fun ξ =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg ‖f n ξ‖))))
  · intro ε hε
    let δ := ε / (2 * (M + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨C, _hC, hc⟩ := homogeneousLowEnergy_interpolation a k δ ha ha1 hk hδ
    have hsmall := (hlow.const_mul C).eventually
      (gt_mem_nhds (show C * 0 < ε / 2 by simpa only [mul_zero] using half_pos hε))
    have hδM : δ * M ≤ ε / 2 := by
      have he : δ * (2 * (M + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith [hδ.le]
    filter_upwards [hsmall] with n hn
    have hi := hc (f n) (h0 n) (hh n)
    have hh' := mul_le_mul_of_nonneg_left (hhigh n) hδ.le
    linarith

end DefocusingNLS

end OAI
