import OAI.Probability.SLE.Loewner.InitialForwardKernelLimit
import OAI.Probability.SLE.Loewner.CapacityParameterContinuity
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! The Loewner right derivative in the exact capacity clock. No
regularity of the driving function is assumed for this identification. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma capacityParameterOnPrefix_tendsto_Ioc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s T : unitInterval} (hsT : s<T) :
    Tendsto (capacityParameterOnPrefix p hi h0 hH T)
      (𝓝[Ioc (initialCapacity p hi h0 hH s) (initialCapacity p hi h0 hH T)]
        (initialCapacity p hi h0 hH s)) (𝓝[Ioc s T] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh := ((capacityParameterOnPrefix_continuous p hi h0 hH T).tendsto
      (initialCapacity p hi h0 hH s)).mono_left
        (show 𝓝[Ioc (initialCapacity p hi h0 hH s) (initialCapacity p hi h0 hH T)]
          (initialCapacity p hi h0 hH s)≤𝓝 (initialCapacity p hi h0 hH s) from inf_le_left)
    rwa [capacityParameterOnPrefix_at_initialCapacity p hi h0 hH T hsT.le] at hh
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact capacityParameterOnPrefix_mem_Ioc p hi h0 hH T hc

theorem capacityForward_quotient_tendsto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s T : unitInterval} (hsT : s<T) (hT : T<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    Tendsto (fun c : ℝ =>
      (capacityForwardOnPrefix p hi h0 hH T z c-
        capacityForwardOnPrefix p hi h0 hH T z (initialCapacity p hi h0 hH s))/
      ((c-initialCapacity p hi h0 hH s:ℝ):ℂ))
      (𝓝[Ioc (initialCapacity p hi h0 hH s) (initialCapacity p hi h0 hH T)]
        (initialCapacity p hi h0 hH s))
      (𝓝 (1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)))) := by
  have hh := (initialForward_quotient_tendsto p hi h0 hH hsT hT hz).comp
    (capacityParameterOnPrefix_tendsto_Ioc p hi h0 hH hsT)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcap := capacityParameterOnPrefix_capacity p hi h0 hH T
    (show c∈Icc 0 (initialCapacity p hi h0 hH T) from
      ⟨(initialCapacity_nonneg p hi h0 hH s).trans hc.1.le,hc.2⟩)
  simp only [comp_apply,hcap,capacityForwardOnPrefix_at_initialCapacity p hi h0 hH T z hsT.le]
  rfl

theorem capacityForward_hasDerivWithinAt_right (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s T : unitInterval} (hsT : s<T) (hT : T<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    HasDerivWithinAt (capacityForwardOnPrefix p hi h0 hH T z)
      (1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)))
      (Ioc (initialCapacity p hi h0 hH s) (initialCapacity p hi h0 hH T))
      (initialCapacity p hi h0 hH s) := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have hh := capacityForward_quotient_tendsto p hi h0 hH hsT hT hz
  have he : slope (capacityForwardOnPrefix p hi h0 hH T z) (initialCapacity p hi h0 hH s)=
      fun c : ℝ => (capacityForwardOnPrefix p hi h0 hH T z c-
        capacityForwardOnPrefix p hi h0 hH T z (initialCapacity p hi h0 hH s))/
        ((c-initialCapacity p hi h0 hH s:ℝ):ℂ) := by
    funext c
    simp only [slope_def_module,Complex.real_smul,ofReal_inv,div_eq_mul_inv,mul_comm]
  rw [he]
  exact hh

end SLEExactGauge

end

end OAI
