import OAI.NumberTheory.Jacobsthal.Probability.StateKernelInvariance

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InitialDensityFormulas
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.WeightFutureIntegrals NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.RegenerationTails NumberTheoryLean.TwoStepDensityBounds
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.OrdinaryKernelInvariance

noncomputable def initialTwoDensity (s : EvenState) (t : ℝ) : ℝ :=
  (Ici (2 : ℝ)).indicator (fun t ↦ (W t * phiEven t / phiEven s.1) * wMass (s.1 - 1) (t + 1)) t

noncomputable def regTwoDensity (u : ℝ) : ℝ :=
  (Ici (1 : ℝ)).indicator (fun u ↦ (W u * phiOdd u / sieveA) * tailW u) u

noncomputable def regThreeDensity (t : ℝ) : ℝ :=
  (Ici (2 : ℝ)).indicator (fun t ↦ (W t * phiEven t / sieveA) * regIntegral t) t

noncomputable def initialIncoming (s : EvenState) (t u : ℝ) : ℝ :=
  TransitionKernels.evenDensity s u * transitionDensity .odd (oddLift u).1 t

noncomputable def regTwoIncoming (u y : ℝ) : ℝ :=
  TransitionKernels.oddDensity regenerationState y * transitionDensity .even (evenLift y).1 u

noncomputable def regThreeIncoming (t u : ℝ) : ℝ :=
  regTwoDensity u * transitionDensity .odd (oddLift u).1 t

theorem regTwoDensity_measurable : Measurable regTwoDensity :=
  (((W_measurable.mul phiOdd_continuous.measurable).div_const sieveA).mul tailW_measurable).indicator measurableSet_Ici

theorem regTwoDensity_nonneg (u : ℝ) : 0 ≤ regTwoDensity u := by
  by_cases hu : 1 ≤ u
  · rw [regTwoDensity, indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu)]
    exact mul_nonneg (div_nonneg (mul_nonneg (W_pos (by linarith)).le (phiOdd_pos u).le) sieveA_pos.le)
      (tailW_nonneg hu)
  · rw [regTwoDensity, indicator_of_notMem (show u ∉ Ici (1 : ℝ) from hu)]

theorem initialIncoming_formula (s : EvenState) {t : ℝ} (ht : 2 ≤ t) (u : ℝ) :
    initialIncoming s t u = (Icc (s.1 - 1) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / phiEven s.1) * W u) u := by
  classical
  by_cases hu : s.1 - 1 ≤ u
  · have hlift : (oddLift u).1 = u := max_eq_right (by linarith [s.2])
    by_cases hut : u ≤ t + 1
    · rw [initialIncoming, hlift, indicator_of_mem (show u ∈ Icc (s.1 - 1) (t + 1) from ⟨hu, hut⟩)]
      change transitionDensity .even s.1 u * transitionDensity .odd u t = _
      have htwo := two_step_density_eq (i := .even) (s := s.1) (t := u) (u := t) s.2 hu
        (show max 2 (u - 1) ≤ t from max_le ht (by linarith))
      simp only [Side.flip, weight] at htwo
      exact htwo.trans (by ring)
    · have hn : t ∉ Ici (max 2 (u - 1)) := by
        intro h
        have := le_trans (le_max_right (2 : ℝ) (u - 1)) h
        linarith
      rw [initialIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
        TransitionKernels.tailDensity, indicator_of_notMem hn, mul_zero,
        indicator_of_notMem (show u ∉ Icc (s.1 - 1) (t + 1) from fun h ↦ hut h.2)]
  · rw [initialIncoming, TransitionKernels.evenDensity, TransitionKernels.tailDensity,
      indicator_of_notMem (show u ∉ Ici (s.1 - 1) from hu), zero_mul,
      indicator_of_notMem (show u ∉ Icc (s.1 - 1) (t + 1) from fun h ↦ hu h.1)]

theorem initialIncoming_zero (s : EvenState) {t : ℝ} (ht : t < 2) (u : ℝ) : initialIncoming s t u = 0 := by
  unfold initialIncoming transitionDensity
  simp only [minRatio, weight, Side.flip, TransitionKernels.tailDensity]
  rw [indicator_of_notMem (show t ∉ Ici (max 2 ((oddLift u).1 - 1)) from fun h ↦
    (not_le_of_gt ht) (le_trans (le_max_left _ _) h)), mul_zero]

theorem regTwoIncoming_formula (u y : ℝ) :
    regTwoIncoming u y = (Icc (2 : ℝ) (u + 1)).indicator
      (fun y ↦ (W u * phiOdd u / sieveA) * W y) y := by
  classical
  have hmin : max 2 (regenerationState.1 - 1) = 2 := by norm_num [regenerationState]
  by_cases hy : 2 ≤ y
  · have hlift : (evenLift y).1 = y := max_eq_right (by linarith)
    by_cases hyu : y ≤ u + 1
    · rw [regTwoIncoming, hlift, indicator_of_mem (show y ∈ Icc (2 : ℝ) (u + 1) from ⟨hy, hyu⟩)]
      change transitionDensity .odd regenerationState.1 y * transitionDensity .even y u = _
      have htwo := two_step_density_eq (i := .odd) (s := regenerationState.1) (t := y) (u := u)
        regenerationState.2 (by simpa only [minRatio, hmin] using hy) (by change y - 1 ≤ u; linarith)
      simp only [Side.flip, weight] at htwo
      rw [phiOdd_initial (s := regenerationState.1) (by norm_num [regenerationState])] at htwo
      exact htwo.trans (by ring)
    · rw [regTwoIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
        TransitionKernels.tailDensity,
        indicator_of_notMem (show u ∉ Ici (y - 1) by change ¬y - 1 ≤ u; linarith), mul_zero,
        indicator_of_notMem (show y ∉ Icc (2 : ℝ) (u + 1) from fun h ↦ hyu h.2)]
  · rw [regTwoIncoming, TransitionKernels.oddDensity, TransitionKernels.tailDensity, hmin,
      indicator_of_notMem (show y ∉ Ici (2 : ℝ) from hy), zero_mul,
      indicator_of_notMem (show y ∉ Icc (2 : ℝ) (u + 1) from fun h ↦ hy h.1)]

theorem regTwoIncoming_zero {u : ℝ} (hu : u < 1) (y : ℝ) : regTwoIncoming u y = 0 := by
  have hmin : max 2 (regenerationState.1 - 1) = 2 := by norm_num [regenerationState]
  by_cases hy : 2 ≤ y
  · have hlift : (evenLift y).1 = y := max_eq_right (by linarith)
    rw [regTwoIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
      TransitionKernels.tailDensity,
      indicator_of_notMem (show u ∉ Ici (y - 1) by change ¬y - 1 ≤ u; linarith), mul_zero]
  · rw [regTwoIncoming, TransitionKernels.oddDensity, TransitionKernels.tailDensity, hmin,
      indicator_of_notMem (show y ∉ Ici (2 : ℝ) from hy), zero_mul]

theorem regThreeIncoming_formula {t : ℝ} (ht : 2 ≤ t) (u : ℝ) :
    regThreeIncoming t u = (Icc (1 : ℝ) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / sieveA) * (W u * tailW u)) u := by
  classical
  by_cases hu : 1 ≤ u
  · have hlift : (oddLift u).1 = u := max_eq_right (by linarith)
    by_cases hut : u ≤ t + 1
    · rw [regThreeIncoming, regTwoDensity, indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu), hlift,
        transitionDensity, minRatio, weight, Side.flip, weight, TransitionKernels.tailDensity,
        indicator_of_mem (show t ∈ Ici (max 2 (u - 1)) from max_le ht (by linarith)),
        indicator_of_mem (show u ∈ Icc (1 : ℝ) (t + 1) from ⟨hu, hut⟩)]
      field_simp [(phiOdd_pos u).ne', sieveA_pos.ne']
    · have hn : t ∉ Ici (max 2 (u - 1)) := by
        intro h
        have := le_trans (le_max_right (2 : ℝ) (u - 1)) h
        linarith
      rw [regThreeIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
        TransitionKernels.tailDensity, indicator_of_notMem hn, mul_zero,
        indicator_of_notMem (show u ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hut h.2)]
  · rw [regThreeIncoming, regTwoDensity, indicator_of_notMem (show u ∉ Ici (1 : ℝ) from hu), zero_mul,
      indicator_of_notMem (show u ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hu h.1)]

theorem regThreeIncoming_zero {t : ℝ} (ht : t < 2) (u : ℝ) : regThreeIncoming t u = 0 := by
  unfold regThreeIncoming transitionDensity
  simp only [minRatio, weight, Side.flip, TransitionKernels.tailDensity]
  rw [indicator_of_notMem (show t ∉ Ici (max 2 ((oddLift u).1 - 1)) from fun h ↦
    (not_le_of_gt ht) (le_trans (le_max_left _ _) h)), mul_zero]

end Erdos970Dependency.InitialDensityFormulas

end

section

open Set MeasureTheory
namespace Erdos970Dependency.CompactIncomingIntegrals
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.InitialDensityFormulas

theorem initialIncoming_integrable (s : EvenState) (t : ℝ) : Integrable (initialIncoming s t) := by
  by_cases ht : 2 ≤ t
  · rw [show initialIncoming s t = (Icc (s.1 - 1) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / phiEven s.1) * W u) from funext (initialIncoming_formula s ht)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    have hu0 : 0 < u := by linarith [s.2, hu.1]
    exact (continuousAt_const.mul (W_continuousAt (ne_of_gt hu0))).continuousWithinAt
  · rw [show initialIncoming s t = 0 from funext (initialIncoming_zero s (lt_of_not_ge ht))]
    exact integrable_zero _ _ _

theorem regTwoIncoming_integrable (u : ℝ) : Integrable (regTwoIncoming u) := by
  by_cases hu : 1 ≤ u
  · rw [show regTwoIncoming u = (Icc (2 : ℝ) (u + 1)).indicator
      (fun y ↦ (W u * phiOdd u / NumberTheoryLean.BuchstabBridge.sieveA) * W y)
      from funext (regTwoIncoming_formula u)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    apply ContinuousOn.integrableOn_Icc
    intro y hy
    exact (continuousAt_const.mul (W_continuousAt (by linarith [hy.1]))).continuousWithinAt
  · rw [show regTwoIncoming u = 0 from funext (regTwoIncoming_zero (lt_of_not_ge hu))]
    exact integrable_zero _ _ _

theorem regThreeIncoming_integrable (t : ℝ) : Integrable (regThreeIncoming t) := by
  by_cases ht : 2 ≤ t
  · rw [show regThreeIncoming t = (Icc (1 : ℝ) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / NumberTheoryLean.BuchstabBridge.sieveA) * (W u * tailW u))
      from funext (regThreeIncoming_formula ht)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact ((regKernel_continuousOn (b := t + 1) (by norm_num : (0 : ℝ) < 1)).const_mul _).integrableOn_Icc
  · rw [show regThreeIncoming t = 0 from funext (regThreeIncoming_zero (lt_of_not_ge ht))]
    exact integrable_zero _ _ _

theorem initialIncoming_integral (s : EvenState) (hsup : s.1 ≤ 23 / 10) (t : ℝ) :
    (∫ u, initialIncoming s t u) = initialTwoDensity s t := by
  by_cases ht : 2 ≤ t
  · simp_rw [initialIncoming_formula s ht]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show s.1 - 1 ≤ t + 1 by linarith),
      initialTwoDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    rfl
  · simp only [initialIncoming_zero s (lt_of_not_ge ht), integral_zero]
    rw [initialTwoDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht)]

theorem regTwoIncoming_integral (u : ℝ) : (∫ y, regTwoIncoming u y) = regTwoDensity u := by
  by_cases hu : 1 ≤ u
  · simp_rw [regTwoIncoming_formula]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ u + 1 by linarith),
      regTwoDensity, indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu), tailW_eq_mass hu]
    rfl
  · simp only [regTwoIncoming_zero (lt_of_not_ge hu), integral_zero]
    rw [regTwoDensity, indicator_of_notMem (show u ∉ Ici (1 : ℝ) from hu)]

theorem regThreeIncoming_integral (t : ℝ) : (∫ u, regThreeIncoming t u) = regThreeDensity t := by
  by_cases ht : 2 ≤ t
  · simp_rw [regThreeIncoming_formula ht]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (1 : ℝ) ≤ t + 1 by linarith),
      regThreeDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    rfl
  · simp only [regThreeIncoming_zero (lt_of_not_ge ht), integral_zero]
    rw [regThreeDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht)]

end Erdos970Dependency.CompactIncomingIntegrals

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.MarginalDensityMeasures
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.KernelDensityBridge NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.DensityConservation
open Erdos970Dependency.InitialDensityFormulas Erdos970Dependency.CompactIncomingIntegrals

noncomputable def initialTwoMeasure (s : EvenState) : Measure ℝ := oddRealKernel ∘ₘ evenKernel s
noncomputable def regTwoMeasure : Measure ℝ := evenRealKernel ∘ₘ oddKernel regenerationState
noncomputable def regThreeMeasure : Measure ℝ := oddRealKernel ∘ₘ regTwoMeasure

instance initialTwoMeasure_isProbabilityMeasure (s : EvenState) : IsProbabilityMeasure (initialTwoMeasure s) := by
  unfold initialTwoMeasure
  infer_instance
instance regTwoMeasure_isProbabilityMeasure : IsProbabilityMeasure regTwoMeasure := by unfold regTwoMeasure; infer_instance
instance regThreeMeasure_isProbabilityMeasure : IsProbabilityMeasure regThreeMeasure := by unfold regThreeMeasure; infer_instance

theorem even_input_measurable (s : EvenState) : Measurable (evenDensity s) :=
  evenDensity_measurable.comp (measurable_const.prodMk measurable_id)

theorem odd_input_measurable (s : OddState) : Measurable (oddDensity s) :=
  oddDensity_measurable.comp (measurable_const.prodMk measurable_id)

theorem evenKernel_eq_density (s : EvenState) :
    evenKernel s = volume.withDensity (fun u ↦ ENNReal.ofReal (evenDensity s u)) := by
  ext B hB
  rw [evenKernel_apply, withDensity_apply _ hB]

theorem oddKernel_eq_density (s : OddState) :
    oddKernel s = volume.withDensity (fun u ↦ ENNReal.ofReal (oddDensity s u)) := by
  ext B hB
  rw [oddKernel_apply, withDensity_apply _ hB]

theorem odd_lifted_density_measurable :
    Measurable (fun z : ℝ × ℝ ↦ transitionDensity .odd (oddLift z.1).1 z.2) :=
  (transitionDensity_joint_measurable .odd).comp
    (((measurable_subtype_coe.comp oddLift_measurable).comp measurable_fst).prodMk measurable_snd)

theorem even_lifted_density_measurable :
    Measurable (fun z : ℝ × ℝ ↦ transitionDensity .even (evenLift z.1).1 z.2) :=
  (transitionDensity_joint_measurable .even).comp
    (((measurable_subtype_coe.comp evenLift_measurable).comp measurable_fst).prodMk measurable_snd)

theorem initialTwoMeasure_eq_density (s : EvenState) (hsup : s.1 ≤ 23 / 10) :
    initialTwoMeasure s = volume.withDensity (fun t ↦ ENNReal.ofReal (initialTwoDensity s t)) := by
  rw [initialTwoMeasure, evenKernel_eq_density]
  apply kernel_density_conservation oddRealKernel (evenDensity s) (initialTwoDensity s)
    (fun u t ↦ transitionDensity .odd (oddLift u).1 t) (even_input_measurable s) (evenDensity_nonneg s)
  · exact ((even_input_measurable s).comp measurable_fst).mul odd_lifted_density_measurable
  · intro u B _
    exact oddKernel_apply (oddLift u) B
  · intro t
    exact initialIncoming_integrable s t
  · intro u t
    exact mul_nonneg (evenDensity_nonneg s u) (oddDensity_nonneg (oddLift u) t)
  · intro t
    exact initialIncoming_integral s hsup t

theorem regTwoMeasure_eq_density :
    regTwoMeasure = volume.withDensity (fun u ↦ ENNReal.ofReal (regTwoDensity u)) := by
  rw [regTwoMeasure, oddKernel_eq_density]
  apply kernel_density_conservation evenRealKernel (oddDensity regenerationState) regTwoDensity
    (fun y u ↦ transitionDensity .even (evenLift y).1 u)
    (odd_input_measurable regenerationState) (oddDensity_nonneg regenerationState)
  · exact ((odd_input_measurable regenerationState).comp measurable_fst).mul even_lifted_density_measurable
  · intro y B _
    exact evenKernel_apply (evenLift y) B
  · intro u
    exact regTwoIncoming_integrable u
  · intro y u
    exact mul_nonneg (oddDensity_nonneg regenerationState y) (evenDensity_nonneg (evenLift y) u)
  · intro u
    exact regTwoIncoming_integral u

theorem regThreeMeasure_eq_density :
    regThreeMeasure = volume.withDensity (fun t ↦ ENNReal.ofReal (regThreeDensity t)) := by
  rw [regThreeMeasure, regTwoMeasure_eq_density]
  apply kernel_density_conservation oddRealKernel regTwoDensity regThreeDensity
    (fun u t ↦ transitionDensity .odd (oddLift u).1 t) regTwoDensity_measurable regTwoDensity_nonneg
  · exact (regTwoDensity_measurable.comp measurable_fst).mul odd_lifted_density_measurable
  · intro u B _
    exact oddKernel_apply (oddLift u) B
  · intro t
    exact regThreeIncoming_integrable t
  · intro u t
    exact mul_nonneg (regTwoDensity_nonneg u) (oddDensity_nonneg (oddLift u) t)
  · intro t
    exact regThreeIncoming_integral t

end Erdos970Dependency.MarginalDensityMeasures

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.DensityComparison
open NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.TransitionKernels
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.InitialDensityFormulas
open Erdos970Dependency.MarginalDensityMeasures

noncomputable def dominationConstant : ℝ := 48 * sieveA / phiEven (23 / 10)

theorem dominationConstant_pos : 0 < dominationConstant :=
  div_pos (mul_pos (by norm_num) sieveA_pos) (phiEven_pos (by norm_num))

theorem initial_density_le (s : EvenState) (hs : 199 / 100 ≤ s.1) (hsup : s.1 ≤ 23 / 10) (t : ℝ) :
    initialTwoDensity s t ≤ dominationConstant * regThreeDensity t := by
  by_cases ht : 2 ≤ t
  · rw [initialTwoDensity, regThreeDensity,
      indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht), indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    have hnum : 0 < W t * phiEven t := mul_pos (W_pos (by linarith)) (phiEven_pos (by linarith))
    have hden : 0 < phiEven s.1 := phiEven_pos (by linarith)
    have hmin : 0 < phiEven (23 / 10) := phiEven_pos (by norm_num)
    have hdenle : phiEven (23 / 10) ≤ phiEven s.1 :=
      phiEven_strictAntiOn.antitoneOn (by linarith : 1 < s.1) (by norm_num) hsup
    calc
      _ ≤ (W t * phiEven t / phiEven s.1) * (48 * regIntegral t) :=
        mul_le_mul_of_nonneg_left (initial_integral_le hs hsup ht) (div_pos hnum hden).le
      _ ≤ (W t * phiEven t / phiEven (23 / 10)) * (48 * regIntegral t) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hnum.le hmin hdenle)
          (mul_nonneg (by norm_num) (regIntegral_nonneg ht))
      _ = dominationConstant * ((W t * phiEven t / sieveA) * regIntegral t) := by
        unfold dominationConstant
        field_simp [sieveA_pos.ne', hmin.ne']
  · rw [initialTwoDensity, regThreeDensity,
      indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht),
      indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht), mul_zero]

theorem initial_real_measure_le (s : EvenState) (hs : 199 / 100 ≤ s.1) (hsup : s.1 ≤ 23 / 10) :
    initialTwoMeasure s ≤ ENNReal.ofReal dominationConstant • regThreeMeasure := by
  rw [initialTwoMeasure_eq_density s hsup, regThreeMeasure_eq_density,
    ← withDensity_smul' (ENNReal.ofReal dominationConstant) (fun t ↦ ENNReal.ofReal (regThreeDensity t)) ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro t
  change ENNReal.ofReal (initialTwoDensity s t) ≤ ENNReal.ofReal dominationConstant * ENNReal.ofReal (regThreeDensity t)
  rw [← ENNReal.ofReal_mul dominationConstant_pos.le]
  exact ENNReal.ofReal_le_ofReal (initial_density_le s hs hsup t)

end Erdos970Dependency.DensityComparison

end

end Erdos970

end OAI
