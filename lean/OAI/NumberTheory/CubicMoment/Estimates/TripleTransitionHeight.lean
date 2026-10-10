import OAI.NumberTheory.CubicMoment.Estimates.PrimeTransitionHeight

namespace OAI

/-! Coarse height means for the actual two-prime/one-prime product at
the transition, used only in the complementary Mellin integral. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma two_prime_unit_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, 2 < x → W i x = 0) (hW : ∀ i x, ‖W i x‖ ≤ 1) :
    (∑ a ∈ fullSquarefreePrimeSupport 2 W X 1, ‖fullPrimeCoefficient 2 W X a‖^2) ≤
      1152*(∏ i, X i) := by
  have hb (a : Eisenstein) : ‖fullPrimeCoefficient 2 W X a‖ ≤ 4 := by
    have hh := fullPrimeCoefficient_norm_bound 2 W X (fun _ => 1) (fun _ => zero_le_one) hW a
    simpa [hcard] using hh
  have hm := fullPrimeCoefficient_l1_unit (by norm_num : (0:ℝ) ≤ 2) W X hX hlo hhi hW 1
  rw [hcard] at hm
  norm_num [primeCoefficientMassConstant] at hm
  calc
    _ ≤ ∑ a ∈ fullSquarefreePrimeSupport 2 W X 1, 4*‖fullPrimeCoefficient 2 W X a‖ :=
      Finset.sum_le_sum (fun a _ => by nlinarith [_root_.norm_nonneg (fullPrimeCoefficient 2 W X a),hb a])
    _ = 4*(∑ a ∈ fullSquarefreePrimeSupport 2 W X 1, ‖fullPrimeCoefficient 2 W X a‖) := by rw [Finset.mul_sum]
    _ ≤ 4*(288*(∏ i, X i)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

theorem two_prime_transition_height {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) :
    ∃ (η K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u T : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      B₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
      (1+Real.log (L r))^m ≤ T → T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (∏ i, XA i) = A → (∀ i, 0 < XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      dyadicHeightMean (fun t =>
        ‖fullPrimeProductGauss 2 WA (fun _ : Unit => W r) XA (fun _ => L r) (u+t)‖) T ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ) := by
  obtain ⟨η,K,B₀,m,hη,hη1,hK,hvar⟩ := single_prime_transition_height_variance
    hpub hHuxley hperiod hMV hC hGI hGQ L W hL hW hlo hhi hW1
  refine ⟨η,2*(Real.sqrt (1152*K)+1),B₀,m,hη,hη1,by positivity,?_⟩
  intro r A u T WA XA hB₀ hrough hAlo hAhi hT hThi hu hprod hXA hAlow hAhigh hWA
  let P := fullSquarefreePrimeSupport 2 WA XA 1
  let α := fullPrimeCoefficient 2 WA XA
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  let V := fun x => (dispersionCutoff 4 x:ℂ)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hP (a : Eisenstein) (ha : a ∈ P) : primary a ∧ norm a/A ∈ Set.Icc 1 4 := by
    have hn := fullPrimeProduct_norm_bounds 2 WA XA hXA hAlow hAhigh (Finset.mem_filter.mp ha).1
    rw [hprod,hcard] at hn
    norm_num at hn
    exact ⟨(fullSquarefreePrimeSupport_primary 2 WA XA 1 ha).1,
      (le_div_iff₀ hA).mpr (by simpa using hn.1),(div_le_iff₀ hA).mpr hn.2⟩
  have hS (b : Eisenstein) (hb : b ∈ S) : primary b :=
    (fullSquarefreePrimeSupport_primary 2 (fun _ : Unit => W r) (fun _ => L r) 1 hb).1
  have he := two_prime_unit_energy hcard WA XA hXA hAlow hAhigh hWA
  rw [hprod] at he
  have hv := hvar r A u T hB₀ hrough hAlo hAhi hT hThi hu
  have herror := height_bilinear_full_variance_bound_sq P S α β u (fun a ha => (hP a ha).1) hS
    (dispersionCutoff 4) (dispersionCutoff_nonneg 4) (dispersionCutoff_complex_compact 4)
    (dispersionCutoff_complex_smooth 4) hA hTp
    (fun a ha => by rw [dispersionCutoff_one (hP a ha).2])
  have hc : Continuous (fun t => fullPrimeProductGauss 2 WA (fun _ : Unit => W r) XA (fun _ => L r) (u+t)) :=
    (continuous_fullPrimeProductGauss _ _ _ _ _).comp (continuous_const.add continuous_id)
  have hvc : Continuous (fun t : ℝ =>
      ‖smoothedDispersionVariance S β (u+t) V A‖) := ((continuous_smoothedDispersionVariance S hS β V (dispersionCutoff_complex_compact 4)
    (dispersionCutoff_complex_smooth 4) hA).comp (continuous_const.add continuous_id)).norm
  have hh := height_bilinear_error_log_saving hc hTp (by norm_num : (0:ℝ) ≤ 1152)
    hK.le hA hB hz 0 0 (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (dyadicHeightMean_nonneg hvc hTp (fun _ => _root_.norm_nonneg _)) herror
    (by simpa only [pow_zero,mul_one] using he) (by simpa only [mul_zero,zero_mul,add_zero,zero_add,pow_zero,div_one] using hv)
  simpa only [pow_zero,div_one] using hh

end CubicFirstMoment

end

end OAI
