import OAI.NumberTheory.Jacobsthal.Renewal.RegenerationDrift

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CompactExponentialMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels RegenerationTails RegenerationDrift

theorem exponential_moment_of_upper_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≤ ENNReal.ofReal (2 * Real.exp m) := by
  let q : ℝ → ℝ := fun x => max m x
  have hq : Measurable q := measurable_const.max measurable_id
  let ν := μ.map q
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (μ := μ) hq.aemeasurable).mpr inferInstance
  have hs : ∀ᵐ x ∂ν, m ≤ x := by
    apply (ae_map_iff hq.aemeasurable measurableSet_Ici).mpr
    exact Eventually.of_forall (fun x => le_max_left m x)
  have ht : ∀ h : ℝ, 0 ≤ h → ν (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h)) := by
    intro h hh
    by_cases h0 : h = 0
    · subst h
      simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact le_trans (measure_mono (subset_univ _)) (by rw [measure_univ])
    · change μ.map q (Ici (m + h)) ≤ _
      rw [Measure.map_apply hq measurableSet_Ici]
      have hpre : q ⁻¹' Ici (m + h) = Ici (m + h) := by
        ext x
        change (m + h ≤ max m x) ↔ m + h ≤ x
        rw [le_max_iff]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exfalso
            have hh0 : 0 < h := lt_of_le_of_ne hh (Ne.symm h0)
            linarith
          · exact hx
        · exact Or.inr
      rw [hpre]
      exact htail h hh
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (q x)) ∂μ := lintegral_mono (fun x =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_max_right m x)))
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂ν :=
      (lintegral_map (ENNReal.measurable_ofReal.comp Real.measurable_exp) hq).symm
    _ ≤ _ := exponential_moment_of_tail ν m hs ht

theorem exponential_integrable_of_upper_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    Integrable Real.exp μ := by
  refine ⟨Real.continuous_exp.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => (Real.exp_pos x).le))).mpr
  exact lt_of_le_of_lt (exponential_moment_of_upper_tail μ m htail) ENNReal.ofReal_lt_top

theorem evenKernel_tail_above (s : EvenState) {v : ℝ} (hv : s.1 ≤ v) :
    evenKernel s (Ici (v - 1)) = ENNReal.ofReal (phiEven v / phiEven s.1) := by
  have h := evenKernel_tail s (sub_nonneg.mpr hv)
  rw [show s.1 - 1 + (v - s.1) = v - 1 by ring,
    show s.1 + (v - s.1) = v by ring] at h
  exact h

theorem oddKernel_tail_above (s : OddState) {v : ℝ} (hv : max 3 s.1 ≤ v) :
    oddKernel s (Ici (v - 1)) = ENNReal.ofReal (phiOdd v / phiOdd s.1) := by
  rw [oddKernel_apply, ← ofReal_integral_eq_lintegral_ofReal
    (oddDensity_integrable s).integrableOn (Eventually.of_forall (oddDensity_nonneg s))]
  congr 1
  change (∫ t in Ici (v - 1), tailDensity (max 2 (s.1 - 1)) (phiOdd s.1)
    (fun t => W t * phiEven t) t) = _
  have hv3 := le_trans (le_max_left (3 : ℝ) s.1) hv
  have hvs := le_trans (le_max_right (3 : ℝ) s.1) hv
  rw [tailDensity_setIntegral (by apply max_le <;> linarith), integral_Ici_eq_integral_Ioi]
  have hf := (phiOdd_future_integral v).2
  rw [max_eq_right (show 2 ≤ v - 1 by linarith)] at hf
  rw [← hf]

theorem kernel_uniform_upper_tails : ∃ U : ℝ, 4 ≤ U ∧
    (∀ V : ℝ, U ≤ V → ∀ s : EvenState, s.1 ≤ V → ∀ h : ℝ, 0 ≤ h →
      evenKernel s (Ici (V - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) ∧
    (∀ V : ℝ, U ≤ V → ∀ s : OddState, s.1 ≤ V → ∀ h : ℝ, 0 ≤ h →
      oddKernel s (Ici (V - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) := by
  obtain ⟨U, hU, hb⟩ := weights_logDeriv_growth 2
  refine ⟨U, hU, ?_, ?_⟩
  · intro V hV s hs h hh
    rw [show V - 1 + h = V + h - 1 by ring, evenKernel_tail_above s (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiEven_pos (by linarith [s.2]))).mpr
    have hx := exponential_comparison (P := phiEven)
      (fun t ht => phiEven_pos (by linarith))
      (fun t ht => (phiEven_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).1) hV (show V ≤ V + h by linarith)
    rw [add_sub_cancel_left] at hx
    have hm : phiEven V ≤ phiEven s.1 :=
      phiEven_strictAntiOn.antitoneOn (by change 1 < s.1; linarith [s.2]) (by change 1 < V; linarith) hs
    exact le_trans hx (by nlinarith [mul_le_mul_of_nonneg_right hm (Real.exp_pos (-2 * h)).le])
  · intro V hV s hs h hh
    rw [show V - 1 + h = V + h - 1 by ring, oddKernel_tail_above s (by apply max_le <;> linarith)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiOdd_pos s.1)).mpr
    have hx := exponential_comparison (P := phiOdd) (fun t _ => phiOdd_pos t)
      (fun t ht => (phiOdd_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).2) hV (show V ≤ V + h by linarith)
    rw [add_sub_cancel_left] at hx
    have hm := phiOdd_antitone hs
    exact le_trans hx (by nlinarith [mul_le_mul_of_nonneg_right hm (Real.exp_pos (-2 * h)).le])

theorem kernel_compact_exponential_moments (S : ℝ) : ∃ C : ℝ, 0 < C ∧
    (∀ s : EvenState, s.1 ≤ S → Integrable Real.exp (evenKernel s) ∧
      (∫ t, Real.exp t ∂evenKernel s) ≤ C) ∧
    (∀ s : OddState, s.1 ≤ S → Integrable Real.exp (oddKernel s) ∧
      (∫ t, Real.exp t ∂oddKernel s) ≤ C) := by
  obtain ⟨U, _, he, ho⟩ := kernel_uniform_upper_tails
  let V := max U S
  let C := 2 * Real.exp (V - 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    have ht := he V (le_max_left _ _) s (le_trans hs (le_max_right _ _))
    have hi := exponential_integrable_of_upper_tail (evenKernel s) (V - 1) ht
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hC.le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact exponential_moment_of_upper_tail _ (V - 1) ht
  · intro s hs
    have ht := ho V (le_max_left _ _) s (le_trans hs (le_max_right _ _))
    have hi := exponential_integrable_of_upper_tail (oddKernel s) (V - 1) ht
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hC.le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact exponential_moment_of_upper_tail _ (V - 1) ht

theorem kernel_global_drift : ∃ C : ℝ, 0 < C ∧
    (∀ s : EvenState, Integrable Real.exp (evenKernel s) ∧
      (∫ t, Real.exp t ∂evenKernel s) ≤ driftFactor * Real.exp s.1 + C) ∧
    (∀ s : OddState, Integrable Real.exp (oddKernel s) ∧
      (∫ t, Real.exp t ∂oddKernel s) ≤ driftFactor * Real.exp s.1 + C) := by
  obtain ⟨U, _, he, ho⟩ := kernel_drift_expectation
  obtain ⟨C, hC, heC, hoC⟩ := kernel_compact_exponential_moments U
  refine ⟨C, hC, ?_, ?_⟩
  · intro s
    by_cases hs : U ≤ s.1
    · exact ⟨(he s hs).1, by linarith [(he s hs).2]⟩
    · exact ⟨(heC s (le_of_not_ge hs)).1, by
        nlinarith [(heC s (le_of_not_ge hs)).2, mul_pos driftFactor_pos (Real.exp_pos s.1)]⟩
  · intro s
    by_cases hs : U ≤ s.1
    · exact ⟨(ho s hs).1, by linarith [(ho s hs).2]⟩
    · exact ⟨(hoC s (le_of_not_ge hs)).1, by
        nlinarith [(hoC s (le_of_not_ge hs)).2, mul_pos driftFactor_pos (Real.exp_pos s.1)]⟩

end NumberTheoryLean.CompactExponentialMoments

end

end Erdos970

end OAI
