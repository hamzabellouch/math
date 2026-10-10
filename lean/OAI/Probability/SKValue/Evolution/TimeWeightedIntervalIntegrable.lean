import Mathlib
import OAI.Probability.SKValue.Equations.IntegralAbsSqrtSecond
import OAI.Probability.SKValue.Processes.StripPaths

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma OrderParameter.time_weighted_intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable (fun t ↦ t*γ.coeff t) volume 0 1 := by
  simpa only [mul_comm, id_eq] using γ.intervalIntegrable.mul_continuousOn continuous_id.continuousOn

lemma OrderParameter.time_weighted_terminal (γ : OrderParameter) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, t*γ.coeff t) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..1, t*γ.coeff t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    γ.time_weighted_intervalIntegrable (show (0 : ℝ)∈uIcc (0 : ℝ) 1 from left_mem_uIcc)
  have ht : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝[uIcc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, by
      simpa only [id_eq, uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using eventually_time_mem⟩
  exact Filter.Tendsto.comp (hc 1 right_mem_uIcc) ht

theorem IsDiffusion.parisi_first_value {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hstrips : ∀ T : ℝ, 0<T → T<1 → ∃ K L Kg Lg Lu : ℝ,
      ValueStrip T γ.coeff (phi W γ) K L ∧
      GradientStrip T γ.coeff (gradient W γ) Kg Lg ∧ 0≤Lu ∧
      ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|))
    (hmoment : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t := by
  have hid : ∀ T∈Ioo (0 : ℝ) 1, (∫ ω, phi W γ T (X T ω) ∂W.μ)=
      phi W γ 0 0+(1/2 : ℝ)*(∫ t in (0 : ℝ)..T, t*γ.coeff t) := by
    intro T hT
    obtain ⟨K,L,Kg,Lg,Lu,hV,hG,hLu,hu⟩ := hstrips T hT.1 hT.2
    have hh := hX.value_expectation hT.1 hT.2 hV hG hLu hu
    rw [hh]
    congr 2
    apply intervalIntegral.integral_congr_Ioo_of_le hT.1.le
    intro t ht
    change γ.coeff t*(∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t*γ.coeff t
    rw [hmoment t ⟨ht.1.le,ht.2.trans hT.2⟩, mul_comm]
  have hlim : Tendsto (fun T ↦ ∫ ω, phi W γ T (X T ω) ∂W.μ) (𝓝[<] (1 : ℝ))
      (𝓝 (phi W γ 0 0+(1/2 : ℝ)*(∫ t in (0 : ℝ)..1, t*γ.coeff t))) := by
    apply ((γ.time_weighted_terminal.const_mul (1/2 : ℝ)).const_add (phi W γ 0 0)).congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
    exact (hid T hT).symm
  have he := tendsto_nhds_unique hX.phi_expectation_terminal hlim
  unfold parisi
  linarith

end SKValue

end

end OAI
