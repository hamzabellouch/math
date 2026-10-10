import OAI.Probability.SLE.Stochastic.PlanarCompensated
import OAI.Probability.SLE.Stochastic.PlanarCutoffStop

namespace OAI

/-! The full-past martingale associated with each compact smooth planar
test. This supplies conditional optional sampling at localization times. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planarWiener_frozen_measurable (T : ℝ≥0) :
    @Measurable (ℝ×(Driver×Driver)) (ℝ×ℝ)
      ((borel ℝ).prod (planarWienerFiltration T)) inferInstance
      (fun p => planarWiener (min p.1.toNNReal T) p.2) := by
  have hp := (Filtration.stronglyAdapted_natural (fun t =>
    (measurable_planarWiener t).stronglyMeasurable)).isStronglyProgressive_of_continuous
      planarWiener_continuous
  let : MeasurableSpace (Driver×Driver) := planarWienerFiltration T
  have ht : Measurable (fun p : ℝ×(Driver×Driver) =>
      ((⟨min p.1.toNNReal T,mem_Iic.mpr (min_le_right _ _)⟩ : Iic T),p.2)) :=
    ((measurable_fst.real_toNNReal.min measurable_const).subtype_mk).prodMk measurable_snd
  exact (hp T).measurable.comp ht

lemma planar_compensator_adapted (f : ℝ×ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (T : ℝ≥0) : Measurable[planarWienerFiltration T]
      (fun b => ∫ u in (0:ℝ)..(T:ℝ), planarGenerator f (planarWiener u.toNNReal b)) := by
  let : MeasurableSpace (Driver×Driver) := planarWienerFiltration T
  let G (u : ℝ) (b : Driver×Driver) := planarGenerator f (planarWiener (min u.toNNReal T) b)
  have hm : Measurable (Function.uncurry G) :=
    (planarGenerator_smooth f hf).continuous.measurable.comp (planarWiener_frozen_measurable T)
  have hi := (cumulative_integral_measurable G hm).comp
    ((measurable_const (a := T)).prodMk measurable_id)
  have he (b : Driver×Driver) : (∫ u in (0:ℝ)..(T:ℝ), G u b)=
      ∫ u in (0:ℝ)..(T:ℝ), planarGenerator f (planarWiener u.toNNReal b) := by
    apply intervalIntegral.integral_congr_Ioo_of_le T.coe_nonneg
    intro u hu
    have huT : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hu.2.le
    simp only [G,min_eq_left huT]
  change Measurable (fun b => ∫ u in (0:ℝ)..(T:ℝ), G u b) at hi
  simpa only [he] using hi

lemma planar_compensated_stronglyAdapted (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : StronglyAdapted planarWienerFiltration (planarCompensated f) := by
  intro t
  exact ((hf.continuous.measurable.comp (planarWiener_adapted t)).sub
    (planar_compensator_adapted f hf t)).stronglyMeasurable

theorem planar_compensated_martingale
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Martingale (planarCompensated f) planarWienerFiltration (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have ha := planar_compensated_stronglyAdapted f hf
  refine ⟨ha,fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (planarWienerFiltration.le s)
    (planar_compensated_integrable W hW f hf hc t)
    (fun A _ _ => (planar_compensated_integrable W hW f hf hc s).integrableOn)
    ?_ (ha s).aestronglyMeasurable
  intro A hA _
  have hh := planar_compensated_past_integral_zero W hW f hf hc s t hst A hA
  have hi : Integrable (fun b => planarCompensated f t b) ((W.prod W).restrict A) :=
    (planar_compensated_integrable W hW f hf hc t).restrict
  have hj : Integrable (fun b => planarCompensated f s b) ((W.prod W).restrict A) :=
    (planar_compensated_integrable W hW f hf hc s).restrict
  rw [integral_sub hi hj] at hh
  exact (sub_eq_zero.mp hh).symm

end SLEExactGauge

end

end OAI
