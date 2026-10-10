import OAI.MathematicalPhysics.Boltzmann.Branching.Moments
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceMinorization
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

section

/-! # Passing from all compact restrictions to an almost-everywhere assertion -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem ae_of_all_compact_restrict {μ : Measure Published.SpaceTime} {p : Published.SpaceTime → Prop}
    (h : ∀ K : Set Published.SpaceTime, IsCompact K → ∀ᵐ x ∂μ.restrict K, p x) :
    ∀ᵐ x ∂μ, p x := by
  have he : (⋃ n : ℕ, Metric.closedBall (0 : Published.SpaceTime) n) = univ :=
    Metric.iUnion_closedBall_nat 0
  have ht := (ae_restrict_iUnion_iff (fun n : ℕ => Metric.closedBall (0 : Published.SpaceTime) n) p).mpr
    (fun n => h _ (isCompact_closedBall _ _))
  simpa only [he,Measure.restrict_univ] using ht

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Volume domination by the selected two-collision angular window -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localTwoCollisionLaw_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ ball beamAxis δ,
        volume.restrict (ball (0 : V) δ) ≤ B •
          localTwoCollisionLaw v := by
  obtain ⟨d,C,hd,hC0,hCt,hout,hin⟩ := paired_parameterSphere_dominated
  obtain ⟨ε,hε,hεsmall,hgood⟩ := collision_window_good
  obtain ⟨a,δ,K,_ha,hab,hδ,hδa,hK,hvolume⟩ :=
    uniform_family_window_volume (lt_min hd hε)
  have had := hab.trans (min_le_left _ _)
  have haε := hab.trans (min_le_right _ _)
  have hδsmall := hδa.trans (haε.trans hεsmall)
  let I := ENNReal.ofReal (2*δ)
  let B := I⁻¹ * (K : ℝ≥0∞)^3 * (C^2)
  have hI0 : I ≠ 0 := by dsimp [I]; positivity
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) (pow_ne_zero 2 hC0)
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (ENNReal.pow_ne_top hCt)
  refine ⟨δ,B,hδ,hδsmall,hB0,hBt,?_⟩
  intro v hv
  have hupper := familyWindowMap_local_le haε hδa had hCt hgood hout hin hv
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hlower := hvolume v hv (A ∩ ball (0 : V) δ) (hA.inter measurableSet_ball) inter_subset_right
  have hAupper : ((familyWindowMeasure a δ).map (familyWindowMap v)) (A ∩ ball (0 : V) δ) ≤
      (C^2) * localTwoCollisionLaw v A := by
    exact (hupper _).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have htotal : I * volume (A ∩ ball (0 : V) δ) ≤ (K : ℝ≥0∞)^3 *
      ((C^2) * localTwoCollisionLaw v A) := by
    exact hlower.trans (by gcongr)
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹ * (I * volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 *
        ((C^2) * localTwoCollisionLaw v A)) := by gcongr
    _ = B * localTwoCollisionLaw v A := by simp only [B,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform finite-entropy moments give spacetime transport integrability -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem entropyMoment_spacetime_integrable {T : ℝ} {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (F t))
    (hbound : ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ p, entropyMoment (F t) p) ≤ C) :
    Integrable (fun z : ℝ × Phase => entropyMoment (F z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  let E : ℝ × Phase → ℝ := fun z => entropyMoment (F z.1) z.2
  have hEm : Measurable E := by
    unfold E entropyMoment
    exact hFm.mul ((measurable_const.add (measurable_snd.snd.norm.pow_const 2)).add hFm.log.abs)
  have hEn (t : ℝ) (p : Phase) : 0 ≤ E (t,p) := entropyMoment_nonneg (hFn t p)
  obtain ⟨C,hC⟩ := hbound
  apply (integrable_prod_iff hEm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hfinite t ht).2.2
  · apply Integrable.of_bound (hEm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have he : (∫ p, ‖E (t,p)‖) = ∫ p, E (t,p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => Real.norm_of_nonneg (hEn t p))
    rw [he,Real.norm_of_nonneg (integral_nonneg (hEn t))]
    exact hC t ht

theorem mass_transport_integrable {T : ℝ} {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (F z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    Integrable (fun z : ℝ × Phase => F z.1 z.2*φ.transportDerivative z.1 z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  obtain ⟨C,hC,hb⟩ := φ.bounded_on_time T
  apply (hEi.const_mul (2*C)).mono' (hFm.mul φ.measurable_transportDerivative).aestronglyMeasurable
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with z hz
  change ‖F z.1 z.2*φ.transportDerivative z.1 z.2‖ ≤ 2*C*entropyMoment (F z.1) z.2
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hFn z.1 z.2)]
  have hφ := (hb z.1 hz z.2).2
  have hf := hFn z.1 z.2
  have hE := entropyMoment_nonneg hf
  have hv : (1+‖z.2.2‖)*F z.1 z.2 ≤ 2*entropyMoment (F z.1) z.2 := by
    unfold entropyMoment
    have hlog := abs_nonneg (Real.log (F z.1 z.2))
    nlinarith [sq_nonneg (‖z.2.2‖-1),mul_nonneg hf hlog,
      mul_nonneg hf (sq_nonneg (‖z.2.2‖-1))]
  exact (mul_le_mul_of_nonneg_left hφ hf).trans (by nlinarith)

end BoltzmannNonuniqueness

end

end

end OAI
