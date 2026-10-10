import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedCoreDensity

namespace OAI

/-! # The free-core mass bound retains the positive scale in the denominator -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem normalizedCoreKernel_scale_time_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (ht : 0 ≤ t) (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool)
    (x : JetPrototype.Space) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedCoreKernel η K α γ s d q a ((t,x),v) univ ≤
      ENNReal.ofReal (growthConstant K α γ q/(s+t)) := by
  apply (normalizedCoreKernel_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a x hv).trans_eq
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign,← ENNReal.ofReal_toReal (SheetTotal.bound_lt_top q (2*Real.exp (16*(1+α)^2))).ne,
    ← ENNReal.ofReal_mul (amplitude_nonneg hK hs ht α γ)]
  congr 1
  unfold amplitude growthConstant
  ring

theorem kineticFreeKernel_scale_time_bound {K α γ s d q : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool)
    (z : KineticPhase) (ht : 0 ≤ z.1.1) :
    kineticFreeKernel η K α γ s d q a z univ ≤
      ENNReal.ofReal (growthConstant K α γ q/(s+z.1.1)) := by
  by_cases hv : transverse z.2 = 0
  · rw [kineticFreeKernel,ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [kineticFreeKernel,ChartKernel.offAxis_apply _ _ hv,input_kineticColdKernel]
    exact normalizedCoreKernel_scale_time_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a _ hv

theorem dilatedFreeKernel_scale_time_bound {r K α γ s d q : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool)
    (z : KineticPhase) (ht : 0 ≤ z.1.1) :
    dilatedFreeKernel r η K α γ s d q a z univ ≤
      ENNReal.ofReal (growthConstant K α γ q/(z.1.1+s/r)) := by
  by_cases hv : transverse z.2 = 0
  · rw [dilatedFreeKernel,ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [dilatedFreeKernel,ChartKernel.offAxis_apply _ _ hv,ChartKernel.inputKernel_mass,
      dilatedColdKernel_apply,normalizedChartGain,chartGain_smul_measure]
    have hb := kineticFreeKernel_scale_time_bound hK hα hγ hs hd hdmax hq₁ hq₂ η a
      ((r*z.1.1,r • z.1.2),z.2) (mul_nonneg hr.le ht)
    rw [kineticFreeKernel,ChartKernel.offAxis_apply _ ((r*z.1.1,r • z.1.2),z.2) hv,
      ChartKernel.inputKernel_mass] at hb
    apply (mul_le_mul' le_rfl hb).trans_eq
    rw [← ENNReal.ofReal_mul hr.le]
    congr 1
    field_simp
    ring

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
