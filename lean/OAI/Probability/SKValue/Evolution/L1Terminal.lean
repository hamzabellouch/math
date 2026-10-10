import Mathlib
import OAI.Probability.SKValue.Evolution.TimeWeightedIntervalIntegrable
import OAI.Probability.SKValue.Processes.WeightedTerminalExpectation

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

lemma BrownianSpace.L1_terminal (W : BrownianSpace) :
    Tendsto (fun t : ℝ ↦ ∫ ω, |W.B t.toNNReal ω-W.B 1 ω| ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun t : ℝ ↦ (1 : ℝ)-t) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ ↦ (1 : ℝ)-t) (𝓝[<] (1 : ℝ)) (𝓝 (1-1)))
  have hs : Tendsto (fun t : ℝ ↦ Real.sqrt (1-t)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hi
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) ?_ hs
  filter_upwards [eventually_time_mem] with t ht
  simpa only [abs_sub_comm] using brownian_increment_abs_bound W ht

lemma UnitMomentMartingale.terminal_integral_past
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {f : ℝ → Ω → ℝ}
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω|≤1 ∧ Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) {Y : Ω → ℝ}
    (hYm : StronglyMeasurable[ℱ t] Y) (hYi : Integrable Y μ) :
    (∫ ω, U ω*Y ω ∂μ) = ∫ ω, f t ω*Y ω ∂μ := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le 1)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  have hprod : Integrable (fun ω ↦ U ω*Y ω) μ :=
    hYi.bdd_mul (hUm.mono (ℱ.le 1)).aestronglyMeasurable
      (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  have hc := condExp_mul_of_stronglyMeasurable_right hYm hprod hUi
  have he : μ[U*Y | ℱ t] =ᵐ[μ] (fun ω ↦ f t ω*Y ω) := by
    filter_upwards [hc,h.terminal_condExp hUm hU ht] with ω hω hω'
    simpa only [Pi.mul_apply,hω'] using hω
  exact (integral_condExp (ℱ.le t)).symm.trans (integral_congr_ae he)

lemma IsDiffusion.terminal_compact_product {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)))
    {T : ℝ} (hT : 0≤T) (hT1 : T<1)
    (hc : ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Icc (0 : ℝ) T)) :
    (∫ ω, U ω*X T ω ∂W.μ)=(∫ ω, U ω*W.B T.toNNReal ω ∂W.μ)+
      ∫ t in (0 : ℝ)..T, t*γ.coeff t := by
  have hUb : ∀ᵐ ω ∂W.μ, ‖U ω‖≤1 :=
    hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1)
  have hUs : AEStronglyMeasurable U W.μ := (hUm.mono (W.realFiltration.le 1)).aestronglyMeasurable
  have hXi := (hX.memLp ⟨hT,hT1.le⟩ (p := 1) (by norm_num)).integrable le_rfl
  have hBi := ((W.brownian.hasLaw_eval T.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl
  have hγ := γ.intervalIntegrable.mono_set (show uIcc (0 : ℝ) T⊆uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hT,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hT1.le)
  have hd : (fun ω ↦ U ω*(∫ s in (0 : ℝ)..T, γ.coeff s*gradient W γ s (X s ω))) =ᵐ[W.μ]
      (fun ω ↦ U ω*(X T ω-W.B T.toNNReal ω)) := by
    filter_upwards [hX.2] with ω hω
    rw [hω.2 T ⟨hT,hT1.le⟩,add_sub_cancel_left]
  have hi := ((hXi.sub hBi).bdd_mul hUs hUb).congr hd.symm
  calc
    _ = ∫ ω, U ω*W.B T.toNNReal ω+
          U ω*(∫ s in (0 : ℝ)..T, γ.coeff s*gradient W γ s (X s ω)) ∂W.μ := by
      apply integral_congr_ae
      filter_upwards [hX.2] with ω hω
      rw [hω.2 T ⟨hT,hT1.le⟩,mul_add]
    _ = _ := by
      rw [integral_add (hBi.bdd_mul hUs hUb) hi,
        hm.weighted_terminal_expectation hUm hU hT hT1 hc hγ]

lemma IsDiffusion.terminal_product_value {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)))
    (hc : ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Ico (0 : ℝ) 1)) :
    (∫ ω, U ω*X 1 ω ∂W.μ)=(∫ ω, U ω*W.B 1 ω ∂W.μ)+
      ∫ t in (0 : ℝ)..1, t*γ.coeff t := by
  have hUs : AEStronglyMeasurable U W.μ := (hUm.mono (W.realFiltration.le 1)).aestronglyMeasurable
  have hUb := hU.mono (fun _ hω ↦ hω.1)
  have hXlim := bounded_multiplier_integral_tendsto hUs hUb
    (eventually_time_mem.mono (fun t ht ↦ (hX.memLp ht (p := 1) (by norm_num)).integrable le_rfl))
    ((hX.memLp (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1) (p := 1) (by norm_num)).integrable le_rfl)
    hX.L1_terminal
  have hBlim := bounded_multiplier_integral_tendsto hUs hUb
    (Eventually.of_forall (fun t : ℝ ↦ ((W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl))
    (((W.brownian.hasLaw_eval 1).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl) W.L1_terminal
  have he : (fun T ↦ ∫ ω, U ω*X T ω ∂W.μ) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun T ↦ (∫ ω, U ω*W.B T.toNNReal ω ∂W.μ)+∫ t in (0 : ℝ)..T, t*γ.coeff t) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
    exact hX.terminal_compact_product hm hUm hU hT.1.le hT.2
      (hc.mono (fun _ hω ↦ hω.mono (fun _ ht ↦ ⟨ht.1,ht.2.trans_lt hT.2⟩)))
  exact tendsto_nhds_unique hXlim ((hBlim.add γ.time_weighted_terminal).congr' he.symm)

end SKValue

end

end OAI
