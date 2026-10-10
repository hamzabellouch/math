import Mathlib.Probability.Kernel.Composition.MeasureComp
import OAI.NumberTheory.Jacobsthal.Estimates.InvariantFiniteness

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.IncomingDensityIdentities
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.FinitePathGeometry
open Erdos970Dependency.InvariantDensities

noncomputable def incomingOdd (t s : ℝ) : ℝ :=
  oddDensity s * transitionDensity .odd s t
noncomputable def incomingEven (t s : ℝ) : ℝ :=
  evenDensity s * transitionDensity .even s t

theorem incomingOdd_formula {t : ℝ} (ht : 2 ≤ t) (s : ℝ) :
    incomingOdd t s = (Icc (1 : ℝ) (t + 1)).indicator
      (fun s ↦ (W t * phiEven t) * oddFactor s) s := by
  classical
  by_cases hs1 : 1 ≤ s
  · rw [incomingOdd, oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs1)]
    by_cases hst : s ≤ t + 1
    · have hmax : max 2 (s - 1) ≤ t := max_le ht (by linarith)
      rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_mem (show t ∈ Ici (max 2 (s - 1)) from hmax),
        indicator_of_mem (show s ∈ Icc (1 : ℝ) (t + 1) from ⟨hs1, hst⟩)]
      field_simp [(phiOdd_pos s).ne']
    · have hmax : ¬max 2 (s - 1) ≤ t := by
        intro h
        have := le_trans (le_max_right (2 : ℝ) (s - 1)) h
        linarith
      rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_notMem (show t ∉ Ici (max 2 (s - 1)) from hmax),
        indicator_of_notMem (show s ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hst h.2), mul_zero]
  · rw [incomingOdd, oddDensity,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs1), zero_mul,
      indicator_of_notMem (show s ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hs1 h.1)]

theorem incomingEven_formula (t s : ℝ) :
    incomingEven t s = (Icc (2 : ℝ) (t + 1)).indicator (fun _ ↦ W t * phiOdd t) s := by
  classical
  by_cases hs2 : 2 ≤ s
  · rw [incomingEven, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs2)]
    by_cases hst : s ≤ t + 1
    · rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_mem (show t ∈ Ici (s - 1) by change s - 1 ≤ t; linarith),
        indicator_of_mem (show s ∈ Icc (2 : ℝ) (t + 1) from ⟨hs2, hst⟩)]
      field_simp [(phiEven_pos (by linarith : 1 < s)).ne']
    · rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_notMem (show t ∉ Ici (s - 1) by change ¬s - 1 ≤ t; linarith),
        indicator_of_notMem (show s ∉ Icc (2 : ℝ) (t + 1) from fun h ↦ hst h.2), mul_zero]
  · rw [incomingEven, evenDensity,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs2), zero_mul,
      indicator_of_notMem (show s ∉ Icc (2 : ℝ) (t + 1) from fun h ↦ hs2 h.1)]

theorem incomingOdd_zero {t : ℝ} (ht : t < 2) (s : ℝ) : incomingOdd t s = 0 := by
  unfold incomingOdd transitionDensity
  simp only [minRatio, weight, Side.flip, NumberTheoryLean.TransitionKernels.tailDensity]
  rw [indicator_of_notMem (show t ∉ Ici (max 2 (s - 1)) from fun h ↦
    (not_le_of_gt ht) (le_trans (le_max_left _ _) h)), mul_zero]

theorem incomingEven_zero {t : ℝ} (ht : t < 1) (s : ℝ) : incomingEven t s = 0 := by
  by_cases hs : 2 ≤ s
  · unfold incomingEven transitionDensity
    simp only [minRatio, weight, Side.flip, NumberTheoryLean.TransitionKernels.tailDensity]
    rw [indicator_of_notMem (show t ∉ Ici (s - 1) by change ¬s - 1 ≤ t; linarith), mul_zero]
  · rw [incomingEven, evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem incomingOdd_integral (t : ℝ) : (∫ s, incomingOdd t s) = evenDensity t := by
  by_cases ht : 2 ≤ t
  · simp_rw [incomingOdd_formula ht]
    rw [integral_indicator measurableSet_Icc, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show (1 : ℝ) ≤ t + 1 by linarith),
      integral_oddFactor (by linarith : (1 : ℝ) ≤ t + 1),
      evenDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    unfold W
    field_simp
    ring
  · simp only [incomingOdd_zero (lt_of_not_ge ht), integral_zero]
    rw [evenDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht)]

theorem incomingEven_integral (t : ℝ) : (∫ s, incomingEven t s) = oddDensity t := by
  by_cases ht : 1 ≤ t
  · simp_rw [incomingEven_formula]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ t + 1 by linarith),
      intervalIntegral.integral_const, oddDensity, indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht)]
    simp only [smul_eq_mul]
    unfold W oddFactor
    field_simp
    ring
  · simp only [incomingEven_zero (lt_of_not_ge ht), integral_zero]
    rw [oddDensity, indicator_of_notMem (show t ∉ Ici (1 : ℝ) from ht)]

theorem incomingOdd_integrable (t : ℝ) : Integrable (incomingOdd t) := by
  by_cases ht : 2 ≤ t
  · rw [show incomingOdd t = (Icc (1 : ℝ) (t + 1)).indicator
      (fun s ↦ (W t * phiEven t) * oddFactor s) from funext (incomingOdd_formula ht)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    apply ContinuousOn.integrableOn_Icc
    intro s hs
    apply ContinuousAt.continuousWithinAt
    unfold oddFactor
    exact continuousAt_const.mul (continuousAt_const.sub
      (continuousAt_const.div (continuousAt_id.pow 2) (by nlinarith [hs.1])))
  · rw [show incomingOdd t = 0 from funext (incomingOdd_zero (lt_of_not_ge ht))]
    exact integrable_zero _ _ _

theorem incomingEven_integrable (t : ℝ) : Integrable (incomingEven t) := by
  rw [show incomingEven t = (Icc (2 : ℝ) (t + 1)).indicator (fun _ ↦ W t * phiOdd t)
    from funext (incomingEven_formula t)]
  exact (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc

end Erdos970Dependency.IncomingDensityIdentities

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.DensityConservation

theorem kernel_density_conservation (K : Kernel ℝ ℝ) (d e : ℝ → ℝ) (k : ℝ → ℝ → ℝ)
    (hd : Measurable d) (hd0 : ∀ s, 0 ≤ d s)
    (hprod : Measurable (fun z : ℝ × ℝ ↦ d z.1 * k z.1 z.2))
    (hkernel : ∀ s (B : Set ℝ), MeasurableSet B → K s B = ∫⁻ t in B, ENNReal.ofReal (k s t))
    (hint : ∀ t, Integrable (fun s ↦ d s * k s t))
    (hpos : ∀ s t, 0 ≤ d s * k s t)
    (hconserve : ∀ t, (∫ s, d s * k s t) = e t) :
    K ∘ₘ (volume.withDensity (fun s ↦ ENNReal.ofReal (d s))) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (e t)) := by
  apply Measure.ext
  intro B hB
  rw [Measure.bind_apply hB K.aemeasurable]
  have hdensity := lintegral_withDensity_eq_lintegral_mul volume (ENNReal.measurable_ofReal.comp hd)
    (K.measurable_coe hB)
  simp only [Function.comp_def, Pi.mul_apply] at hdensity
  rw [hdensity]
  simp_rw [hkernel _ _ hB]
  have hrewrite (s : ℝ) : ENNReal.ofReal (d s) * (∫⁻ t in B, ENNReal.ofReal (k s t)) =
      ∫⁻ t in B, ENNReal.ofReal (d s * k s t) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    exact (ENNReal.ofReal_mul (hd0 s)).symm
  simp_rw [hrewrite]
  have hm : Measurable (Function.uncurry (fun s t : ℝ ↦ ENNReal.ofReal (d s * k s t))) := by
    change Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (d z.1 * k z.1 z.2))
    simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp hprod
  rw [lintegral_lintegral_swap (μ := volume) (ν := volume.restrict B) hm.aemeasurable]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall (fun s ↦ hpos s _)),
    hconserve]
  exact (withDensity_apply _ hB).symm

end Erdos970Dependency.DensityConservation

end

end Erdos970

end OAI
