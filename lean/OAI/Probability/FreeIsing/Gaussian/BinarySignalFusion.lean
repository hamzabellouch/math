import OAI.Probability.FreeIsing.Gaussian.BinarySignalDensity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

local instance binarySignalFusionMeasurableSingletonSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance binarySignalFusionNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem condDistrib_raw_signal_likelihood
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (S : Ω → IsingSpin) (X : Ω → A) (u : A → ℝ)
    (hS : Measurable S) (hX : Measurable X) (hu : Measurable u)
    (hfair : ∀ a : IsingSpin, (ρ.map S) {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (hpost : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace A).comap X] =ᵐ[ρ] fun ω => u (X ω))
    (a : IsingSpin) :
    condDistrib X S ρ a = (ρ.map X).withDensity
      (fun x => ENNReal.ofReal (1 + spinSign a * u x)) := by
  have hint : Integrable (fun ω => spinSign (S ω)) ρ := by
    apply Integrable.of_bound ((measurable_of_finite spinSign).comp hS).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun ω => by
      cases hs : S ω <;> norm_num [spinSign, hs])
  have hce := condExp_ae_eq_integral_condDistrib hX hS.aemeasurable
    (measurable_of_finite spinSign).stronglyMeasurable hint
  have hprob : ∀ᵐ x ∂ρ.map X, (condDistrib S X ρ x) {a} =
      ENNReal.ofReal ((1 + spinSign a * u x) / 2) := by
    apply (ae_map_iff hX.aemeasurable (measurableSet_eq_fun
      (Kernel.measurable_coe _ (measurableSet_singleton a)) (by fun_prop))).2
    filter_upwards [hpost, hce] with ω hp hc
    rw [spin_measure_singleton_eq_mean, ← hc, hp]
  have hnonzero : (ρ.map S) {a} ≠ 0 := by rw [hfair]; norm_num
  ext E hE
  have hrectangle : (ρ.map (fun ω => (S ω, X ω))) ({a} ×ˢ E) =
      ∫⁻ x in E, condDistrib S X ρ x {a} ∂ρ.map X := by
    rw [← Measure.compProd_apply_prod hE (measurableSet_singleton a),
      compProd_map_condDistrib hX.aemeasurable hS.aemeasurable,
      Measure.map_apply (hS.prodMk hX) ((measurableSet_singleton a).prod hE),
      Measure.map_apply (hX.prodMk hS) (hE.prod (measurableSet_singleton a))]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, and_comm]
  rw [condDistrib_apply_of_ne_zero hS hX a hnonzero, hfair, hrectangle,
    withDensity_apply _ hE, ← lintegral_const_mul _ (Kernel.measurable_coe _
      (measurableSet_singleton a))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hprob] with x hx
  rw [hx, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem posterior_version_calibrated
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (f : Ω → ℝ) (X : Ω → A) (u : A → ℝ)
    (hX : Measurable X) (hu : Measurable u)
    (hpost : ρ[f | (inferInstance : MeasurableSpace A).comap X] =ᵐ[ρ]
      fun ω => u (X ω)) :
    ρ[f | (inferInstance : MeasurableSpace ℝ).comap (fun ω => u (X ω))] =ᵐ[ρ]
      fun ω => u (X ω) := by
  have hm : MeasurableSpace.comap (fun ω => u (X ω)) (inferInstance : MeasurableSpace ℝ) ≤
      MeasurableSpace.comap X (inferInstance : MeasurableSpace A) :=
    (hu.comp (comap_measurable X)).comap_le
  have htower := condExp_condExp_of_le (μ := ρ) (f := f) hm hX.comap_le
  apply htower.symm.trans
  apply (condExp_congr_ae hpost).trans
  rw [condExp_of_stronglyMeasurable (hm.trans hX.comap_le)
    (comap_measurable (fun ω => u (X ω))).stronglyMeasurable
    (integrable_condExp.congr hpost)]

theorem condExp_raw_pair_eq_binaryFusion
    {Ω A B : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (S : Ω → IsingSpin) (X : Ω → A) (Y : Ω → B) (u : A → ℝ) (v : B → ℝ)
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hu : Measurable u) (hv : Measurable v)
    (hfair : ∀ a : IsingSpin, (ρ.map S) {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (hpostX : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace A).comap X] =ᵐ[ρ] fun ω => u (X ω))
    (hpostY : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace B).comap Y] =ᵐ[ρ] fun ω => v (Y ω))
    (hXY : CondIndepFun ((inferInstance : MeasurableSpace IsingSpin).comap S)
      hS.comap_le X Y ρ)
    (hu1 : ∀ᵐ ω ∂ρ, |u (X ω)| < 1) (hv1 : ∀ᵐ ω ∂ρ, |v (Y ω)| < 1) :
    ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun ω => (X ω, Y ω))] =ᵐ[ρ]
      fun ω => binaryFusion (u (X ω)) (v (Y ω)) := by
  have hμ : ∀ᵐ x ∂ρ.map X, |u x| < 1 :=
    (ae_map_iff hX.aemeasurable (measurableSet_lt hu.abs measurable_const)).2 hu1
  have hν : ∀ᵐ y ∂ρ.map Y, |v y| < 1 :=
    (ae_map_iff hY.aemeasurable (measurableSet_lt hv.abs measurable_const)).2 hv1
  have hfst := (measurePreserving_fst (μ := ρ.map X) (ν := ρ.map Y)).quasiMeasurePreserving.ae hμ
  have hsnd := (measurePreserving_snd (μ := ρ.map X) (ν := ρ.map Y)).quasiMeasurePreserving.ae hν
  have hκ (a : IsingSpin) :
      (condDistrib X S ρ ×ₖ condDistrib Y S ρ) a =
        ((ρ.map X).prod (ρ.map Y)).withDensity
          (fun z => ENNReal.ofReal ((1 + spinSign a * u z.1) * (1 + spinSign a * v z.2))) := by
    rw [Kernel.prod_apply,
      condDistrib_raw_signal_likelihood ρ S X u hS hX hu hfair hpostX a,
      condDistrib_raw_signal_likelihood ρ S Y v hS hY hv hfair hpostY a,
      prod_withDensity (by fun_prop) (by fun_prop)]
    apply withDensity_congr_ae
    filter_upwards [hfst] with z hz
    have hp : 0 ≤ 1 + spinSign a * u z.1 := by
      rcases abs_lt.mp hz with ⟨hl, hu⟩
      cases a <;> simp only [spinSign_neg, spinSign_pos] <;> linarith
    exact (ENNReal.ofReal_mul hp).symm
  have hlaw : ρ.map (fun ω => (S ω, (X ω, Y ω))) =
      (ρ.map S) ⊗ₘ (condDistrib X S ρ ×ₖ condDistrib Y S ρ) := by
    rw [Measure.compProd_eq_comp_prod]
    exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hX hY hS).1 hXY
  exact condExp_spin_eq_binaryFusion_of_likelihood ρ (ρ.map S) hfair
    ((ρ.map X).prod (ρ.map Y)) (condDistrib X S ρ ×ₖ condDistrib Y S ρ)
    S (fun ω => (X ω, Y ω)) hS (hX.prodMk hY) hlaw
    (fun z => u z.1) (fun z => v z.2) (hu.comp measurable_fst)
    (hv.comp measurable_snd) hfst hsnd hκ

theorem calibrated_condIndep_pair_law
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
    (hU1 : ∀ᵐ ω ∂ρ, |U ω| < 1) (hV1 : ∀ᵐ ω ∂ρ, |V ω| < 1) :
    ρ.map (fun ω => (U ω, V ω)) = binaryFusionLaw (ρ.map U) (ρ.map V) := by
  have hμ : ∀ᵐ u ∂ρ.map U, |u| < 1 :=
    (ae_map_iff hU.aemeasurable (measurableSet_lt measurable_id.abs measurable_const)).2 hU1
  have hν : ∀ᵐ v ∂ρ.map V, |v| < 1 :=
    (ae_map_iff hV.aemeasurable (measurableSet_lt measurable_id.abs measurable_const)).2 hV1
  have hlaw : ρ.map (fun ω => (S ω, (U ω, V ω))) =
      (ρ.map S) ⊗ₘ (condDistrib U S ρ ×ₖ condDistrib V S ρ) := by
    rw [Measure.compProd_eq_comp_prod]
    exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hU hV hS).1 hUV
  rw [← Measure.snd_map_prodMk hS (hU.prodMk hV), hlaw, Measure.snd_compProd]
  exact observation_law_eq_binaryFusionLaw (ρ.map S) hfair (ρ.map U) (ρ.map V)
    hμ hν (condDistrib U S ρ ×ₖ condDistrib V S ρ)
    (calibrated_signal_product_likelihood ρ S U V hS hU hV hfair hcalU hcalV)

theorem raw_condIndep_fusion_quadratic_loss
    {Ω A B : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (S : Ω → IsingSpin) (X : Ω → A) (Y : Ω → B) (u : A → ℝ) (v : B → ℝ)
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hu : Measurable u) (hv : Measurable v)
    (hfair : ∀ a : IsingSpin, (ρ.map S) {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (hpostX : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace A).comap X] =ᵐ[ρ] fun ω => u (X ω))
    (hpostY : ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace B).comap Y] =ᵐ[ρ] fun ω => v (Y ω))
    (hXY : CondIndepFun ((inferInstance : MeasurableSpace IsingSpin).comap S)
      hS.comap_le X Y ρ)
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (huθ : ∀ᵐ ω ∂ρ, |u (X ω)| ≤ theta) (hvθ : ∀ᵐ ω ∂ρ, |v (Y ω)| ≤ theta)
    (hvsym : (ρ.map (fun ω => v (Y ω))).map Neg.neg = ρ.map (fun ω => v (Y ω))) :
    (∫ ω, (ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun ω => (X ω, Y ω))] ω)^2 ∂ρ) ≤
      (∫ ω, u (X ω) ^ 2 ∂ρ) + (∫ ω, v (Y ω) ^ 2 ∂ρ) -
        2 * (1 - theta ^ 2) * (∫ ω, u (X ω) ^ 2 ∂ρ) * (∫ ω, v (Y ω) ^ 2 ∂ρ) := by
  let U := fun ω => u (X ω)
  let V := fun ω => v (Y ω)
  have hU : Measurable U := hu.comp hX
  have hV : Measurable V := hv.comp hY
  have hU1 : ∀ᵐ ω ∂ρ, |U ω| < 1 := huθ.mono (fun _ h => h.trans_lt hθ1)
  have hV1 : ∀ᵐ ω ∂ρ, |V ω| < 1 := hvθ.mono (fun _ h => h.trans_lt hθ1)
  have hμ : ∀ᵐ z ∂ρ.map U, |z| ≤ theta :=
    (ae_map_iff hU.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).2 huθ
  have hν : ∀ᵐ z ∂ρ.map V, |z| ≤ theta :=
    (ae_map_iff hV.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).2 hvθ
  have hpair := calibrated_condIndep_pair_law ρ S U V hS hU hV hfair
    (posterior_version_calibrated ρ _ X u hX hu hpostX)
    (posterior_version_calibrated ρ _ Y v hY hv hpostY)
    (hXY.comp hu hv) hU1 hV1
  have hfull := condExp_raw_pair_eq_binaryFusion ρ S X Y u v hS hX hY hu hv
    hfair hpostX hpostY hXY hU1 hV1
  have hm : Measurable (fun z : ℝ × ℝ => binaryFusion z.1 z.2 ^ 2) := by
    unfold binaryFusion
    fun_prop
  have heq : (∫ ω, (ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun ω => (X ω, Y ω))] ω)^2 ∂ρ) =
      ∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw (ρ.map U) (ρ.map V) := by
    calc
      _ = ∫ ω, binaryFusion (U ω) (V ω) ^ 2 ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hfull] with ω hω
        rw [hω]
      _ = _ := by
        rw [← hpair]
        exact (integral_map (hU.prodMk hV).aemeasurable hm.aestronglyMeasurable).symm
  rw [heq]
  have hb := integral_binaryFusion_sq_le_quadratic_loss (ρ.map U) (ρ.map V)
    hθ0 hθ1 hμ hν hvsym
  rw [integral_map hU.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop)),
    integral_map hV.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))] at hb
  exact hb

end Problem367

end

end OAI
