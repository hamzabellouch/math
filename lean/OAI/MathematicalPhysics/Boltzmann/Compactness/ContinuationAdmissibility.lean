import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.Topology.Piecewise

namespace OAI

section

/-! # Pasting a local solution to a global admissible continuation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def continuedEvolution (T : ℝ) (F G : Evolution) : Evolution :=
  fun t => if t ≤ T then F t else G (t-T)

theorem continuedEvolution_of_le {T t : ℝ} (F G : Evolution) (ht : t ≤ T) :
    continuedEvolution T F G t = F t := ite_eq_left ht

theorem continuedEvolution_of_gt {T t : ℝ} (F G : Evolution) (ht : T < t) :
    continuedEvolution T F G t = G (t-T) := ite_eq_right (not_le_of_gt ht)

namespace AdmissibleLocal

variable {T : ℝ} {f₀ : Density} {F G : Evolution}

theorem continued_initial (S : AdmissibleLocal T f₀ F) :
    continuedEvolution T F G 0 = f₀ := by
  rw [continuedEvolution_of_le F G S.strong.positive_time.le]
  exact S.initial

theorem continued_finite_each_time (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) :
    ∀ t ∈ Ici (0:ℝ), FiniteEntropyDatum (continuedEvolution T F G t) := by
  intro t ht
  by_cases h : t ≤ T
  · rw [continuedEvolution_of_le F G h]
    exact S.finite_each_time t ⟨ht,h⟩
  · rw [continuedEvolution_of_gt F G (lt_of_not_ge h)]
    exact H.finite_each_time (t-T) (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))

theorem continued_momentum (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) :
    ∀ t ∈ Ici (0:ℝ), momentum (continuedEvolution T F G t) = momentum f₀ := by
  intro t ht
  by_cases h : t ≤ T
  · rw [continuedEvolution_of_le F G h]
    exact S.momentum_conservation t ⟨ht,h⟩
  · rw [continuedEvolution_of_gt F G (lt_of_not_ge h)]
    exact (H.momentum_conservation (t-T) (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))).trans
      (S.momentum_conservation T ⟨S.strong.positive_time.le,le_rfl⟩)

theorem continued_energy (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) :
    ∀ t ∈ Ici (0:ℝ), energy (continuedEvolution T F G t) ≤ energy f₀ := by
  intro t ht
  by_cases h : t ≤ T
  · rw [continuedEvolution_of_le F G h,S.energy_conservation t ⟨ht,h⟩]
  · rw [continuedEvolution_of_gt F G (lt_of_not_ge h)]
    exact (H.energy_inequality (t-T) (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))).trans_eq
      (S.energy_conservation T ⟨S.strong.positive_time.le,le_rfl⟩)

theorem continued_uniform_moment (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ s ∈ Icc 0 t, (∫ p, entropyMoment (continuedEvolution T F G s) p) ≤ C := by
  obtain ⟨A,hA⟩ := S.uniform_moment
  obtain ⟨B,hB⟩ := H.uniform_moment t ht
  refine ⟨max A B,?_⟩
  intro s hs
  by_cases h : s ≤ T
  · rw [continuedEvolution_of_le F G h]
    exact (hA s ⟨hs.1,h⟩).trans (le_max_left _ _)
  · rw [continuedEvolution_of_gt F G (lt_of_not_ge h)]
    have hsub : s-T ∈ Icc 0 t :=
      ⟨sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)),by linarith [S.strong.positive_time,hs.2]⟩
    exact (hB (s-T) hsub).trans (le_max_right _ _)

end AdmissibleLocal
end BoltzmannNonuniqueness

end

end

section

/-! # The entropy-dissipation inequality survives pasting at the local endpoint -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

private theorem lintegral_Icc_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Icc a c, f s) = (∫⁻ s in Icc a b, f s)+(∫⁻ s in Icc b c, f s) := by
  have hd : Disjoint (Icc a b) (Ioc b c) := disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy.1)
  have he : (volume : Measure ℝ).restrict (Ioc b c) = volume.restrict (Icc b c) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  rw [← Icc_union_Ioc_eq_Icc hab hbc,lintegral_union measurableSet_Ioc hd,he]

private theorem lintegral_translate_interval (τ a b : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Icc a b, f (t+τ)) = ∫⁻ t in Icc (a+τ) (b+τ), f t := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) τ).restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc (a+τ) (b+τ)))
  have he : (fun t : ℝ => t+τ) ⁻¹' Icc (a+τ) (b+τ) = Icc a b := by
    ext t
    simp only [mem_preimage,mem_Icc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [he] at h
  exact (MeasurePreserving.lintegral_map_equiv f (MeasurableEquiv.addRight τ) h).symm

namespace AdmissibleLocal

variable {T : ℝ} {f₀ : Density} {F G : Evolution}

theorem continued_dissipation_before {t : ℝ} (ht : t ≤ T) :
    (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (continuedEvolution T F G s)) =
      ∫⁻ s in Icc (0:ℝ) t, entropyDissipation (F s) := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [continuedEvolution_of_le F G (hs.2.trans ht)]

theorem continued_dissipation_after (S : AdmissibleLocal T f₀ F)
    {t : ℝ} (ht : T ≤ t) :
    (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (continuedEvolution T F G s)) =
      (∫⁻ s in Icc (0:ℝ) T, entropyDissipation (F s))+
      (∫⁻ s in Icc (0:ℝ) (t-T), entropyDissipation (G s)) := by
  rw [lintegral_Icc_split S.strong.positive_time.le ht,continued_dissipation_before le_rfl]
  congr 1
  calc
    _ = ∫⁻ s in Icc T t, entropyDissipation (G (s-T)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) T)] with s hs hne
      rw [continuedEvolution_of_gt F G (lt_of_le_of_ne hs.1 hne.symm)]
    _ = _ := by
      simpa only [zero_add,sub_add_cancel,add_sub_cancel_right] using
        (lintegral_translate_interval T 0 (t-T) (fun s => entropyDissipation (G (s-T)))).symm

theorem continued_entropy (S : AdmissibleLocal T f₀ F) (H : AdmissibleGlobal (F T) G) :
    ∀ t ∈ Ici (0:ℝ),
      ENNReal.ofReal (relativeEntropy (continuedEvolution T F G t))+
        (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (continuedEvolution T F G s)) ≤
          ENNReal.ofReal (relativeEntropy f₀) := by
  intro t ht
  by_cases h : t ≤ T
  · rw [continuedEvolution_of_le F G h,continued_dissipation_before h]
    exact S.entropy_inequality t ⟨ht,h⟩
  · have hpost := H.entropy_inequality (t-T) (sub_nonneg.mpr (lt_of_not_ge h).le)
    have hpre := S.entropy_inequality T ⟨S.strong.positive_time.le,le_rfl⟩
    rw [continuedEvolution_of_gt F G (lt_of_not_ge h),S.continued_dissipation_after (lt_of_not_ge h).le]
    calc
      _ = (ENNReal.ofReal (relativeEntropy (G (t-T)))+
          (∫⁻ s in Icc (0:ℝ) (t-T), entropyDissipation (G s)))+
          (∫⁻ s in Icc (0:ℝ) T, entropyDissipation (F s)) := by ac_rfl
      _ ≤ ENNReal.ofReal (relativeEntropy (F T))+
          (∫⁻ s in Icc (0:ℝ) T, entropyDissipation (F s)) := add_le_add hpost le_rfl
      _ ≤ _ := hpre

end AdmissibleLocal
end BoltzmannNonuniqueness

end

end

section

/-! # Collision-fiber finiteness and separate gain/loss integrability after pasting -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continued_integrableOn {T R : ℝ} (hT : 0 ≤ T) {F G : Evolution}
    (Φ : Density → Phase → ℝ)
    (ha : IntegrableOn (fun z : ℝ × Phase => Φ (F z.1) z.2) (boundedTimes T))
    (hb : IntegrableOn (fun z : ℝ × Phase => Φ (G z.1) z.2) (boundedTimes R)) :
    IntegrableOn (fun z : ℝ × Phase => Φ (continuedEvolution T F G z.1) z.2)
      (boundedTimes R) := by
  have ha' : Integrable (fun z : ℝ × Phase => Φ (F z.1) z.2)
      ((volume.restrict (Icc (0:ℝ) T)).prod volume) := by
    rw [phaseInterval_measure]
    exact ha
  have hb' : Integrable (fun z : ℝ × Phase => Φ (G z.1) z.2)
      ((volume.restrict (Icc (0:ℝ) R)).prod volume) := by
    rw [phaseInterval_measure]
    exact hb
  have he : (fun z : ℝ × Phase => Φ (continuedEvolution T F G z.1) z.2) =
      timePaste T (fun z => Φ (F z.1) z.2) (fun z => Φ (G z.1) z.2) := by
    funext z
    by_cases ht : z.1 ≤ T <;> simp only [continuedEvolution,timePaste,ht,ite_true,ite_false]
  change Integrable _ (volume.restrict (Icc (0:ℝ) R ×ˢ (univ : Set Phase)))
  rw [he,← phaseIntervalBetween_measure]
  exact timePaste_integrable_bounded hT ha' hb'

theorem continued_property_ae {T R : ℝ} (hT : 0 ≤ T) {F G : Evolution}
    (P : Density → Phase → Prop)
    (ha : ∀ᵐ z ∂volume.restrict (boundedTimes T), P (F z.1) z.2)
    (hb : ∀ᵐ z ∂volume.restrict (boundedTimes R), P (G z.1) z.2) :
    ∀ᵐ z ∂volume.restrict (boundedTimes R), P (continuedEvolution T F G z.1) z.2 := by
  have ha' : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) T)).prod volume, P (F z.1) z.2 := by
    rw [phaseInterval_measure]
    exact ha
  have hb' : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) R)).prod volume, P (G z.1) z.2 := by
    rw [phaseInterval_measure]
    exact hb
  have h := timePaste_property_ae hT ha' hb'
  rw [phaseInterval_measure] at h
  filter_upwards [h] with z hz
  by_cases ht : z.1 ≤ T <;>
    simpa only [continuedEvolution,ht,ite_true,ite_false] using hz

namespace LocalMildSolution

theorem divide_relativeDensity_integrable {T : ℝ} {f₀ : Density} {F : Evolution}
    (S : LocalMildSolution T f₀ F) {r : ℝ × Phase → ℝ}
    (hr : IntegrableOn r (boundedTimes T)) :
    IntegrableOn (fun z => r z/(1+relativeDensity F z.1 z.2)) (boundedTimes T) := by
  have hm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by
    unfold maxwellian
    fun_prop
  have hq : Measurable (fun z : ℝ × Phase => 1/(1+relativeDensity F z.1 z.2)) := by
    exact measurable_const.div (measurable_const.add (S.measurable.div hm))
  have hn (z : ℝ × Phase) : 0 ≤ relativeDensity F z.1 z.2 :=
    div_nonneg (S.nonnegative z.1 z.2) (maxwellian_pos z.2.2).le
  have hb : ∀ᵐ z ∂volume.restrict (boundedTimes T),
      ‖1/(1+relativeDensity F z.1 z.2)‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (by linarith [hn z]))]
    exact div_le_self zero_le_one (by linarith [hn z])
  change Integrable (fun z => r z/(1+relativeDensity F z.1 z.2)) _
  simpa only [div_eq_mul_inv,one_mul] using hr.mul_bdd hq.aestronglyMeasurable hb

end LocalMildSolution

namespace AdmissibleLocal

variable {T : ℝ} {f₀ : Density} {F G : Evolution}

theorem continued_collision_fibers (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ p ∂volume.restrict (boundedTimes R),
      Integrable (fun q : Velocity × Sphere => collisionKernel p.2.2 q.1 q.2 *
        continuedEvolution T F G p.1 (p.2.1,scatterLeft p.2.2 q.1 q.2)*
        continuedEvolution T F G p.1 (p.2.1,scatterRight p.2.2 q.1 q.2))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere => collisionKernel p.2.2 q.1 q.2 *
        continuedEvolution T F G p.1 p.2*continuedEvolution T F G p.1 (p.2.1,q.1))
        ((volume : Measure Velocity).prod sphereArea) :=
  continued_property_ae S.strong.positive_time.le
    (fun f p => Integrable (fun q : Velocity × Sphere => collisionKernel p.2 q.1 q.2 *
      f (p.1,scatterLeft p.2 q.1 q.2)*f (p.1,scatterRight p.2 q.1 q.2))
      ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere => collisionKernel p.2 q.1 q.2 *
        f p*f (p.1,q.1)) ((volume : Measure Velocity).prod sphereArea))
    S.collision_fibers (H.collision_fibers R hR)

theorem continued_gain_integrable (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (fun p : SpaceTimePhase => gain (continuedEvolution T F G p.1) p.2.1 p.2.2 /
      (1+relativeDensity (continuedEvolution T F G) p.1 p.2)) (boundedTimes R) :=
  continued_integrableOn S.strong.positive_time.le
    (fun f p => gain f p.1 p.2/(1+f p/maxwellian p.2))
    (S.toLocalMildSolution.divide_relativeDensity_integrable S.strong.gain_integrable)
    (H.gain_integrable R hR)

theorem continued_loss_integrable (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (fun p : SpaceTimePhase => loss (continuedEvolution T F G p.1) p.2.1 p.2.2 /
      (1+relativeDensity (continuedEvolution T F G) p.1 p.2)) (boundedTimes R) :=
  continued_integrableOn S.strong.positive_time.le
    (fun f p => loss f p.1 p.2/(1+f p/maxwellian p.2))
    (S.toLocalMildSolution.divide_relativeDensity_integrable S.strong.loss_integrable)
    (H.loss_integrable R hR)

end AdmissibleLocal
end BoltzmannNonuniqueness

end

end

section

/-! # Pasting the renormalized distributional equation without a boundary defect -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continued_renormalizedIntegrand (T : ℝ) (F G : Evolution)
    (β : Renormalization) (φ : KineticTest) :
    renormalizedIntegrand (continuedEvolution T F G) β φ =
      timePaste T (renormalizedIntegrand F β φ) (renormalizedIntegrand G β (φ.timeShift T)) := by
  funext z
  by_cases ht : z.1 ≤ T
  · simp only [renormalizedIntegrand,relativeDensity,continuedEvolution,timePaste,ht,ite_true]
  · simp only [renormalizedIntegrand,relativeDensity,continuedEvolution,timePaste,ht,ite_false,
      KineticTest.timeShift_transportDerivative,KineticTest.timeShift_toFun,sub_add_cancel]

namespace AdmissibleLocal

variable {T : ℝ} {f₀ : Density} {F G : Evolution}

theorem continued_renormalized_integrable (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand (continuedEvolution T F G) β φ) nonnegativeTimes := by
  have ha : Integrable (renormalizedIntegrand F β φ)
      ((volume.restrict (Icc (0:ℝ) T)).prod volume) := by
    rw [phaseInterval_measure]
    exact S.renormalized_integrable β φ
  have hb : Integrable (renormalizedIntegrand G β (φ.timeShift T))
      ((volume.restrict (Ici (0:ℝ))).prod volume) := by
    rw [phaseHalfLine_measure]
    exact H.renormalized_integrable β (φ.timeShift T)
  change Integrable _ (volume.restrict (Ici (0:ℝ) ×ˢ (univ : Set Phase)))
  rw [continued_renormalizedIntegrand,← phaseHalfLine_measure (0:ℝ)]
  exact (timePaste_integral S.strong.positive_time.le ha hb).1

theorem continued_renormalized_equation (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (β : Renormalization) (φ : KineticTest) :
    (∫ z in nonnegativeTimes, renormalizedIntegrand (continuedEvolution T F G) β φ z)+
      (∫ p, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  have ha : Integrable (renormalizedIntegrand F β φ)
      ((volume.restrict (Icc (0:ℝ) T)).prod volume) := by
    rw [phaseInterval_measure]
    exact S.renormalized_integrable β φ
  have hb : Integrable (renormalizedIntegrand G β (φ.timeShift T))
      ((volume.restrict (Ici (0:ℝ))).prod volume) := by
    rw [phaseHalfLine_measure]
    exact H.renormalized_integrable β (φ.timeShift T)
  have he := (timePaste_integral S.strong.positive_time.le ha hb).2
  rw [← continued_renormalizedIntegrand,phaseHalfLine_measure,phaseInterval_measure] at he
  have hg := H.renormalized_equation β (φ.timeShift T)
  simp only [KineticTest.timeShift_toFun,zero_add] at hg
  have hl := S.renormalized_balance β φ
  change (∫ z in nonnegativeTimes, renormalizedIntegrand (continuedEvolution T F G) β φ z) =
    (∫ z in boundedTimes T, renormalizedIntegrand F β φ z)+
      (∫ z in nonnegativeTimes, renormalizedIntegrand G β (φ.timeShift T) z) at he
  linarith only [he,hg,hl]

end AdmissibleLocal
end BoltzmannNonuniqueness

end

end

section

/-! # Pasting the local mass equation across the continuation time -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continued_massIntegrand (T : ℝ) (F G : Evolution) (φ : MassTest) :
    (fun z : ℝ × Phase => continuedEvolution T F G z.1 z.2*φ.transportDerivative z.1 z.2) =
      timePaste T (fun z => F z.1 z.2*φ.transportDerivative z.1 z.2)
        (fun z => G z.1 z.2*(φ.timeShift T).transportDerivative z.1 z.2) := by
  funext z
  by_cases ht : z.1 ≤ T
  · simp only [continuedEvolution,timePaste,ht,ite_true]
  · simp only [continuedEvolution,timePaste,ht,ite_false,
      MassTest.timeShift_transportDerivative,sub_add_cancel]

namespace AdmissibleLocal

variable {T : ℝ} {f₀ : Density} {F G : Evolution}

theorem continued_mass_integrable (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (φ : MassTest) :
    IntegrableOn (fun z : ℝ × Phase => continuedEvolution T F G z.1 z.2*φ.transportDerivative z.1 z.2)
      nonnegativeTimes := by
  have ha : Integrable (fun z : ℝ × Phase => F z.1 z.2*φ.transportDerivative z.1 z.2)
      ((volume.restrict (Icc (0:ℝ) T)).prod volume) := by
    rw [phaseInterval_measure]
    exact S.local_mass_integrable φ
  have hb : Integrable (fun z : ℝ × Phase => G z.1 z.2*(φ.timeShift T).transportDerivative z.1 z.2)
      ((volume.restrict (Ici (0:ℝ))).prod volume) := by
    rw [phaseHalfLine_measure]
    exact H.local_mass_integrable (φ.timeShift T)
  change Integrable _ (volume.restrict (Ici (0:ℝ) ×ˢ (univ : Set Phase)))
  rw [continued_massIntegrand,← phaseHalfLine_measure (0:ℝ)]
  exact (timePaste_integral S.strong.positive_time.le ha hb).1

theorem continued_mass_equation (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) (φ : MassTest) :
    (∫ z in nonnegativeTimes, continuedEvolution T F G z.1 z.2*φ.transportDerivative z.1 z.2)+
      (∫ p, f₀ p*φ.toFun 0 p.1) = 0 := by
  have ha : Integrable (fun z : ℝ × Phase => F z.1 z.2*φ.transportDerivative z.1 z.2)
      ((volume.restrict (Icc (0:ℝ) T)).prod volume) := by
    rw [phaseInterval_measure]
    exact S.local_mass_integrable φ
  have hb : Integrable (fun z : ℝ × Phase => G z.1 z.2*(φ.timeShift T).transportDerivative z.1 z.2)
      ((volume.restrict (Ici (0:ℝ))).prod volume) := by
    rw [phaseHalfLine_measure]
    exact H.local_mass_integrable (φ.timeShift T)
  have he := (timePaste_integral S.strong.positive_time.le ha hb).2
  rw [← continued_massIntegrand,phaseHalfLine_measure,phaseInterval_measure] at he
  have hg := H.local_mass (φ.timeShift T)
  simp only [MassTest.timeShift_toFun,zero_add] at hg
  have hl := S.local_mass_balance φ
  change (∫ z in nonnegativeTimes, continuedEvolution T F G z.1 z.2*φ.transportDerivative z.1 z.2) =
    (∫ z in boundedTimes T, F z.1 z.2*φ.transportDerivative z.1 z.2)+
      (∫ z in nonnegativeTimes, G z.1 z.2*(φ.timeShift T).transportDerivative z.1 z.2) at he
  linarith only [he,hg,hl]

end AdmissibleLocal
end BoltzmannNonuniqueness

end

end

section

/-! # Measurability of a pasted local and global kinetic solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AdmissibleLocal

theorem continued_measurable {T : ℝ} {f₀ : Density} {F G : Evolution}
    (S : AdmissibleLocal T f₀ F) (H : AdmissibleGlobal (F T) G) :
    AEStronglyMeasurable (fun z : ℝ × Phase => continuedEvolution T F G z.1 z.2)
      (volume.restrict nonnegativeTimes) := by
  let μ : Measure (ℝ × Phase) := volume.restrict nonnegativeTimes
  let A : Set (ℝ × Phase) := {z | z.1 ≤ T}
  have hA : MeasurableSet A := measurableSet_le measurable_fst measurable_const
  have hm : MeasurePreserving (timeTranslation (-T))
      ((volume.restrict (Ici T)).prod (volume : Measure Phase))
      ((volume.restrict (Ici (0:ℝ))).prod (volume : Measure Phase)) := by
    simpa only [add_neg_cancel] using timeTranslation_halfLine (-T) T
  have hG : AEStronglyMeasurable (fun z : ℝ × Phase => G z.1 z.2)
      ((volume.restrict (Ici (0:ℝ))).prod volume) := by
    rw [phaseHalfLine_measure]
    exact H.spacetime_measurable
  have hs := hG.comp_quasiMeasurePreserving hm.quasiMeasurePreserving
  have hs' : AEStronglyMeasurable (fun z : ℝ × Phase => G (z.1-T) z.2)
      (volume.restrict (Ici T ×ˢ (univ : Set Phase))) := by
    simpa only [phaseHalfLine_measure,Function.comp_def,timeTranslation_apply,sub_eq_add_neg] using hs
  have hpost : AEStronglyMeasurable (fun z : ℝ × Phase => G (z.1-T) z.2) (μ.restrict Aᶜ) := by
    apply hs'.mono_measure
    change (volume.restrict nonnegativeTimes).restrict Aᶜ ≤ _
    rw [Measure.restrict_restrict hA.compl]
    apply Measure.restrict_mono _ le_rfl
    intro z hz
    exact ⟨(lt_of_not_ge (show ¬z.1 ≤ T from hz.1)).le,mem_univ _⟩
  have hpre : AEStronglyMeasurable (fun z : ℝ × Phase => F z.1 z.2) (μ.restrict A) :=
    S.measurable.aestronglyMeasurable
  have h := hpre.piecewise hA hpost
  have he : (fun z : ℝ × Phase => continuedEvolution T F G z.1 z.2) =
      A.piecewise (fun z => F z.1 z.2) (fun z => G (z.1-T) z.2) := by
    funext z
    by_cases hz : z.1 ≤ T <;> simp [continuedEvolution,A,hz]
  rw [he]
  exact h

end BoltzmannNonuniqueness.AdmissibleLocal

end

end

section

/-! # Weak continuity of the pasted local and global solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AdmissibleLocal

theorem continued_weak_continuity {T : ℝ} {f₀ : Density} {F G : Evolution}
    (S : AdmissibleLocal T f₀ F) (H : AdmissibleGlobal (F T) G)
    (ψ : Phase → ℝ) (hψ : Measurable ψ) (hb : ∃ C : ℝ, ∀ p, |ψ p| ≤ C) :
    ContinuousOn (fun t => ∫ p, continuedEvolution T F G t p*ψ p) (Ici 0) := by
  let f : ℝ → ℝ := fun t => ∫ p, F t p*ψ p
  let g : ℝ → ℝ := fun t => ∫ p, G (t-T) p*ψ p
  have hf : ContinuousOn f (Ici (0:ℝ) ∩ closure {t | t ≤ T}) := by
    simpa only [show {t : ℝ | t ≤ T} = Iic T from rfl,isClosed_Iic.closure_eq,Ici_inter_Iic] using
      S.toLocalMildSolution.weak_continuity hψ hb
  have hg : ContinuousOn g (Ici (0:ℝ) ∩ closure {t | ¬t ≤ T}) := by
    have hd : ContinuousOn (fun t : ℝ => t-T) (Ici (0:ℝ) ∩ Ici T) := by fun_prop
    have hm : MapsTo (fun t : ℝ => t-T) (Ici (0:ℝ) ∩ Ici T) (Ici 0) := by
      intro t ht
      exact sub_nonneg.mpr (show T ≤ t from ht.2)
    simpa only [not_le,show {t : ℝ | T < t} = Ioi T from rfl,closure_Ioi,g,Function.comp_def] using
      (H.weak_continuity ψ hψ hb).comp hd hm
  have he : ∀ t ∈ Ici (0:ℝ) ∩ frontier {t | t ≤ T}, f t = g t := by
    intro t ht
    have htT : t = T := frontier_Iic_subset T ht.2
    subst t
    dsimp only [f,g]
    simp only [sub_self]
    apply integral_congr_ae
    filter_upwards [H.initial] with p hp
    rw [hp]
  have hc := hf.if he hg
  convert hc using 1
  funext t
  by_cases ht : t ≤ T <;> simp only [continuedEvolution,ht,ite_true,ite_false,f,g]

end BoltzmannNonuniqueness.AdmissibleLocal

end

end

section

/-! # The global pasting preserves the complete common early interval -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AdmissibleLocal

theorem continued_strongEarly {T : ℝ} {f₀ : Density} {F G : Evolution}
    (S : AdmissibleLocal T f₀ F) : StrongEarly T (continuedEvolution T F G) := by
  refine ⟨S.strong.positive_time,?_,?_,?_⟩
  · intro t ht
    apply (S.strong.strong_continuity t ht).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [continuedEvolution_of_le F G ht.2,continuedEvolution_of_le F G hs.2]
  · apply S.strong.gain_integrable.congr
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    rw [continuedEvolution_of_le F G hz.1.2]
  · apply S.strong.loss_integrable.congr
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    rw [continuedEvolution_of_le F G hz.1.2]

end BoltzmannNonuniqueness.AdmissibleLocal

end

end

section

/-! # A genuine global admissible continuation of the constructed local solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AdmissibleLocal

variable {T : ℝ} {f₀ : Density} {F G : Evolution}

theorem continued_admissible (S : AdmissibleLocal T f₀ F)
    (H : AdmissibleGlobal (F T) G) : AdmissibleGlobal f₀ (continuedEvolution T F G) where
  datum := S.datum
  spacetime_measurable := S.continued_measurable H
  finite_each_time := S.continued_finite_each_time H
  initial := Filter.Eventually.of_forall (congrFun S.continued_initial)
  weak_continuity := S.continued_weak_continuity H
  uniform_moment := S.continued_uniform_moment H
  collision_fibers := S.continued_collision_fibers H
  gain_integrable := S.continued_gain_integrable H
  loss_integrable := S.continued_loss_integrable H
  renormalized_integrable := S.continued_renormalized_integrable H
  renormalized_equation := S.continued_renormalized_equation H
  local_mass_integrable := S.continued_mass_integrable H
  local_mass := S.continued_mass_equation H
  momentum_conservation := S.continued_momentum H
  energy_inequality := S.continued_energy H
  entropy_inequality := S.continued_entropy H

/-- A periodic global continuation retains the local solution pointwise through its endpoint,
preserving strong early regularity and any separation. -/
theorem exists_global_extension (S : AdmissibleLocal T f₀ F)
    (hperiodic : PeriodicExistenceInput) :
    ∃ G : Evolution, AdmissibleGlobal f₀ G ∧ StrongEarly T G ∧
      ∀ t ∈ Icc 0 T, G t = F t := by
  obtain ⟨H,hH⟩ := hperiodic (F T) (S.finite_each_time T ⟨S.strong.positive_time.le,le_rfl⟩)
  exact ⟨continuedEvolution T F H,S.continued_admissible hH,S.continued_strongEarly,
    fun _ ht => continuedEvolution_of_le F H ht.2⟩

end BoltzmannNonuniqueness.AdmissibleLocal

end

end

end OAI
