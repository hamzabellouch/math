import OAI.Probability.FreeIsing.Conditioning.DiscreteConditioning
import OAI.Probability.FreeIsing.Gaussian.BinaryFusionInformation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

local instance binarySignalDensityMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩
local instance binarySignalDensityNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem spin_measure_singleton_eq_mean (τ : Measure IsingSpin) [IsProbabilityMeasure τ]
    (a : IsingSpin) :
    τ {a} = ENNReal.ofReal ((1 + spinSign a * ∫ s, spinSign s ∂τ) / 2) := by
  have hsum : τ {IsingSpin.neg} + τ {IsingSpin.pos} = 1 := by
    have h : (∑ s : IsingSpin, τ {s}) = 1 := by simp
    simpa only [sum_isingSpin] using h
  have hsumreal : (τ {IsingSpin.neg}).toReal + (τ {IsingSpin.pos}).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]
    norm_num
  rw [integral_fintype Integrable.of_finite, sum_isingSpin]
  simp only [measureReal_def, smul_eq_mul, spinSign_neg, spinSign_pos]
  rw [← ENNReal.ofReal_toReal (measure_ne_top τ {a})]
  congr 1
  cases a <;> simp only [spinSign_neg, spinSign_pos] <;> linarith

theorem condDistrib_spin_singleton_of_calibration
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (S : Ω → IsingSpin) (U : Ω → ℝ) (hS : Measurable S) (hU : Measurable U)
    (hcal : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap U] =ᵐ[ρ] U) (a : IsingSpin) :
    ∀ᵐ u ∂ρ.map U, (condDistrib S U ρ u) {a} =
      ENNReal.ofReal ((1 + spinSign a * u) / 2) := by
  have hint : Integrable (fun ω => spinSign (S ω)) ρ := by
    apply Integrable.of_bound ((measurable_of_finite spinSign).comp hS).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun ω => by cases hs : S ω <;> norm_num [spinSign, hs])
  have hpost := condExp_ae_eq_integral_condDistrib hU hS.aemeasurable
    (measurable_of_finite spinSign).stronglyMeasurable hint
  apply (ae_map_iff hU.aemeasurable (measurableSet_eq_fun
    (Kernel.measurable_coe _ (measurableSet_singleton a)) (by fun_prop))).2
  filter_upwards [hcal, hpost] with ω hc hp
  rw [spin_measure_singleton_eq_mean]
  rw [← hp, hc]

theorem condDistrib_signal_eq_withDensity_of_calibration
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (S : Ω → IsingSpin) (U : Ω → ℝ) (hS : Measurable S) (hU : Measurable U)
    (hfair : ∀ a : IsingSpin, (ρ.map S) {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (hcal : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap U] =ᵐ[ρ] U) (a : IsingSpin) :
    condDistrib U S ρ a = (ρ.map U).withDensity
      (fun u => ENNReal.ofReal (1 + spinSign a * u)) := by
  have hnonzero : (ρ.map S) {a} ≠ 0 := by rw [hfair]; norm_num
  have hpost := condDistrib_spin_singleton_of_calibration ρ S U hS hU hcal a
  ext A hA
  have hrectangle : (ρ.map (fun ω => (S ω, U ω))) ({a} ×ˢ A) =
      ∫⁻ u in A, condDistrib S U ρ u {a} ∂ρ.map U := by
    rw [← Measure.compProd_apply_prod hA (measurableSet_singleton a),
      compProd_map_condDistrib hU.aemeasurable hS.aemeasurable,
      Measure.map_apply (hS.prodMk hU) ((measurableSet_singleton a).prod hA),
      Measure.map_apply (hU.prodMk hS) (hA.prod (measurableSet_singleton a))]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, and_comm]
  rw [condDistrib_apply_of_ne_zero hS hU a hnonzero, hfair, hrectangle,
    withDensity_apply _ hA, ← lintegral_const_mul _ (Kernel.measurable_coe _
      (measurableSet_singleton a))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hpost] with u hu
  rw [hu, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem ae_abs_le_one_of_spin_calibration
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    (S : Ω → IsingSpin) (U : Ω → ℝ)
    (hcal : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap U] =ᵐ[ρ] U) :
    ∀ᵐ ω ∂ρ, |U ω| ≤ 1 := by
  have hb : ∀ᵐ ω ∂ρ, |ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap U] ω| ≤ 1 := by
    apply ae_bdd_abs_condExp_of_ae_bdd_abs
    exact Filter.Eventually.of_forall (fun ω => by
      cases hs : S ω <;> norm_num [spinSign, hs])
  filter_upwards [hb, hcal] with ω hb hc
  rwa [hc] at hb

theorem calibrated_signal_product_likelihood
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (S : Ω → IsingSpin) (U V : Ω → ℝ)
    (hS : Measurable S) (hU : Measurable U) (hV : Measurable V)
    (hfair : ∀ a : IsingSpin, (ρ.map S) {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (hcalU : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap U] =ᵐ[ρ] U)
    (hcalV : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap V] =ᵐ[ρ] V) (a : IsingSpin) :
    (condDistrib U S ρ ×ₖ condDistrib V S ρ) a =
      ((ρ.map U).prod (ρ.map V)).withDensity
        (fun z => ENNReal.ofReal ((1 + spinSign a * z.1) * (1 + spinSign a * z.2))) := by
  rw [Kernel.prod_apply,
    condDistrib_signal_eq_withDensity_of_calibration ρ S U hS hU hfair hcalU a,
    condDistrib_signal_eq_withDensity_of_calibration ρ S V hS hV hfair hcalV a,
    prod_withDensity (by fun_prop) (by fun_prop)]
  apply withDensity_congr_ae
  have hUbound : ∀ᵐ u ∂ρ.map U, |u| ≤ 1 :=
    (ae_map_iff hU.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).2
      (ae_abs_le_one_of_spin_calibration ρ S U hcalU)
  have hfst := (measurePreserving_fst (μ := ρ.map U) (ν := ρ.map V)).quasiMeasurePreserving.ae hUbound
  filter_upwards [hfst] with z hz
  have hp : 0 ≤ 1 + spinSign a * z.1 := by
    rcases abs_le.mp hz with ⟨hl, hu⟩
    cases a <;> simp only [spinSign_neg, spinSign_pos] <;> linarith
  exact (ENNReal.ofReal_mul hp).symm

theorem calibrated_condIndep_fusion_quadratic_loss
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (S : Ω → IsingSpin) (U V : Ω → ℝ)
    (hS : Measurable S) (hU : Measurable U) (hV : Measurable V)
    (hfair : ∀ a : IsingSpin, (ρ.map S) {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (hcalU : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap U] =ᵐ[ρ] U)
    (hcalV : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap V] =ᵐ[ρ] V)
    (hUV : CondIndepFun ((inferInstance : MeasurableSpace IsingSpin).comap S)
      hS.comap_le U V ρ)
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hUθ : ∀ᵐ ω ∂ρ, |U ω| ≤ theta) (hVθ : ∀ᵐ ω ∂ρ, |V ω| ≤ theta)
    (hVsym : (ρ.map V).map Neg.neg = ρ.map V) :
    (∫ ω, (ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace (ℝ × ℝ)).comap (fun ω => (U ω, V ω))] ω)^2 ∂ρ) ≤
      (∫ ω, U ω ^ 2 ∂ρ) + (∫ ω, V ω ^ 2 ∂ρ) -
        2 * (1 - theta ^ 2) * (∫ ω, U ω ^ 2 ∂ρ) * (∫ ω, V ω ^ 2 ∂ρ) := by
  have hμ : ∀ᵐ u ∂ρ.map U, |u| ≤ theta :=
    (ae_map_iff hU.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).2 hUθ
  have hν : ∀ᵐ v ∂ρ.map V, |v| ≤ theta :=
    (ae_map_iff hV.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).2 hVθ
  have hlaw : ρ.map (fun ω => (S ω, (U ω, V ω))) =
      (ρ.map S) ⊗ₘ (condDistrib U S ρ ×ₖ condDistrib V S ρ) := by
    rw [Measure.compProd_eq_comp_prod]
    exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hU hV hS).1 hUV
  have hb := integral_condExp_spin_sq_le_quadratic_loss ρ (ρ.map S) hfair
    (ρ.map U) (ρ.map V) hθ0 hθ1 hμ hν hVsym
    (condDistrib U S ρ ×ₖ condDistrib V S ρ)
    (calibrated_signal_product_likelihood ρ S U V hS hU hV hfair hcalU hcalV)
    S (fun ω => (U ω, V ω)) hS (hU.prodMk hV) hlaw
  rw [integral_map hU.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop)),
    integral_map hV.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))] at hb
  exact hb

end Problem367

end

end OAI
