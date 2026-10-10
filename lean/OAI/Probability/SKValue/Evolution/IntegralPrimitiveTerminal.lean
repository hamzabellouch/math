import Mathlib
import OAI.Probability.SKValue.Control.StripRegularity

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
open scoped Topology NNReal

lemma integral_primitive_terminal {f : ℝ → ℝ} (hi : IntervalIntegrable f volume 0 1) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, f t) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (0 : ℝ)∈uIcc (0 : ℝ) 1 from left_mem_uIcc)
  have ht : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝[uIcc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, by
      simpa only [id_eq,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using eventually_time_mem⟩
  exact Filter.Tendsto.comp (hc 1 right_mem_uIcc) ht

theorem IsDiffusion.parisi_value_assembly {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t)
    (hamom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    ∃ U : W.Ω → ℝ,
      Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
      (∀ᵐ ω ∂W.μ, |U ω|≤1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω)-U ω)^2 ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) ∧
      parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t ∧
      parisi W γ=∫ ω, U ω*W.B 1 ω ∂W.μ ∧
      parisi W γ=∫ t in (0 : ℝ)..1, ∫ ω, curvature W γ t (X t ω) ∂W.μ ∧
      IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1 ∧
      Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (parisi W γ)) := by
  obtain ⟨U,hUm,hmart,hU,hU2⟩ := hX.exists_gradient_terminal hreg.core hmom
  have hUmr : StronglyMeasurable[W.realFiltration 1] U := by
    change StronglyMeasurable[W.filtration ((1 : ℝ).toNNReal)] U
    rw [Real.toNNReal_one]
    exact hUm
  have hs : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)) :=
    hU.mono (fun _ hω ↦ ⟨hω.1,hω.2.2.comp terminalTime_tendsto⟩)
  have hm := hX.unitMomentMartingale hreg.core hmom
  have hc := hX.gradient_continuous (fun T hT ↦ by
    obtain ⟨K,L,Lu,hLu,hG,hu⟩ := hreg.core T hT
    exact ⟨Lu,hLu,hu⟩)
  have hP := hX.parisi_first_value (fun T hT hT1 ↦ by
    obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
    exact ⟨Kv,Lv,K,L,Lu,hV,hG,hLu,fun t ht s hs x y ↦ hu s hs t ht y x⟩) hmom
  have hUX := hX.terminal_gradient_product (Eventually.of_forall (fun ω ↦ by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with t ht
    obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg t ⟨ht.1.le,ht.2⟩
    exact ((hV.smooth t ⟨ht.1.le,le_rfl⟩).differentiable (by norm_num)).differentiableAt))
    (hU.mono (fun _ hω ↦ hω.2.2))
  have hid := hX.terminal_product_value hm hUmr hs hc
  rw [integral_congr_ae hUX] at hid
  have hPB : parisi W γ=∫ ω, U ω*W.B 1 ω ∂W.μ := by linarith
  have hi := hX.curvature_mean_integrable hreg hamom
  have hCov := hX.curvature_integral_terminal hreg hm hUmr hs
  have he := tendsto_nhds_unique hCov (integral_primitive_terminal hi)
  exact ⟨U,hmart,hU,hU2,hP,hPB,hPB.trans he,hi,by simpa only [←hPB] using hCov⟩

end SKValue

end

end OAI
