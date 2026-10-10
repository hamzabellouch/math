import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusCharacteristic

namespace OAI

section

/-! # The actual periodic approximations satisfy a spacetime mild identity -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusFlight

theorem initialDensity_measurable {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀) (q : ℝ) :
    Measurable (initialDensity q f₀) := by
  have hp : Measurable JetPeriodicDatum.phaseMap := by
    convert EuclideanFlight.phaseEquiv.measurable using 1
    funext p
    exact (EuclideanFlight.phaseEquiv_apply p).symm
  exact ((ChartKernel.measurable_H q).comp measurable_snd).mul
    (hf₀.comp (hp.comp TorusChart.phase_measurePreserving.measurable))

theorem spacetime_mild (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (_hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    along (regroup (JetCopyDatum.torusPhysical q F.value)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => initialDensity q f₀ z.2 +
      Published.timePrimitive (volume.restrict (Icc 0 T))
        (along (regroup (CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)))) z) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hm := JetCopyDatum.torusPhysical_measurable F.measurable_value q
  have hrm := CollisionCompactness.collisionSource_measurable hm b
  have hreg : Measurable (regroup (JetCopyDatum.torusPhysical q F.value)) :=
    hm.comp MeasurableEquiv.prodAssoc.symm.measurable
  have hsr : Measurable (regroup (CollisionCompactness.collisionSource b
      (JetCopyDatum.torusPhysical q F.value))) := hrm.comp MeasurableEquiv.prodAssoc.symm.measurable
  have hAm := hreg.comp (along_measurePreserving μ).measurable
  have hBm := ((initialDensity_measurable hf₀ q).comp measurable_snd).add
    (Published.timePrimitive_measurable μ (hsr.comp (along_measurePreserving μ).measurable))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have h := characteristic hcarleman F hq₁ hq₂ hb hR ht.1 (ht.2.trans hTU) hloss hf₀
  filter_upwards [h] with p hp
  change along (regroup (JetCopyDatum.torusPhysical q F.value)) (t,p) =
    initialDensity q f₀ p + Published.timePrimitive (volume.restrict (Icc 0 T))
      (along (regroup (CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)))) (t,p)
  rw [Published.timePrimitive_eq_interval ht]
  exact hp

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Free torus flight preserves each fixed velocity restriction -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.TorusFlight

theorem flight_measurePreserving_velocity (t : ℝ) (ν : Measure Velocity) [SFinite ν] :
    MeasurePreserving (flight t) ((volume : Measure Position).prod ν)
      ((volume : Measure Position).prod ν) := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : Position) =>
      x+torusProjection (t • v))) := by
    unfold Function.uncurry torusProjection
    fun_prop
  have hskew := (MeasurePreserving.id ν).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right (volume : Measure Position)
      (torusProjection (t • v))).map_eq))
  have he : flight t = Prod.swap ∘ (fun z : Velocity × Position =>
      (z.1,z.2+torusProjection (t • z.1))) ∘ Prod.swap := rfl
  rw [he]
  exact (Measure.measurePreserving_swap (μ := ν) (ν := (volume : Measure Position))).comp
    (hskew.comp Measure.measurePreserving_swap)

theorem along_measurePreserving_velocity (μ : Measure ℝ) (ν : Measure Velocity)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight z.1 z.2))
      (μ.prod ((volume : Measure Position).prod ν))
      (μ.prod ((volume : Measure Position).prod ν)) :=
  (MeasurePreserving.id μ).skew_product measurable_flight
    (ae_of_all _ (fun t => (flight_measurePreserving_velocity t ν).map_eq))

theorem alongRegroup_measurePreserving (μ : Measure ℝ) (ν : Measure Velocity)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun z : ℝ × Phase => ((z.1,(flight z.1 z.2).1),z.2.2))
      (μ.prod ((volume : Measure Position).prod ν)) ((μ.prod volume).prod ν) :=
  (measurePreserving_prodAssoc μ (volume : Measure Position) ν).symm.comp
    (along_measurePreserving_velocity μ ν)

theorem strong_along_regroup {μ : Measure ℝ} {ν : Measure Velocity} [SFinite μ] [SFinite ν]
    {f : ℕ → (ℝ × Position) × Velocity → ℝ} {g : (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 ((μ.prod volume).prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (along (regroup (f n))-along (regroup g))
      1 (μ.prod ((volume : Measure Position).prod ν))) atTop (𝓝 0) := by
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  exact (eLpNorm_comp_measurePreserving ((hfm n).sub hgm).aestronglyMeasurable
    (alongRegroup_measurePreserving μ ν)).symm

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # L1 bounds for a localized Euclidean lift of a torus density -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.TorusKineticChart

theorem eLpNorm_liftDensity {T : ℝ} {f : (ℝ × Position) × Velocity → ℝ} (hf : Measurable f) :
    eLpNorm (liftDensity f) 1 (cellVolume T) =
      eLpNorm f 1 ((AnnularEnvelope.timePositionVolume T).prod volume) := by
  have h := eLpNorm_comp_measurePreserving (liftDensity_measurable hf).aestronglyMeasurable
    (measurePreserving T) (p := (1:ℝ≥0∞))
  simpa only [liftDensity_comp] using h.symm

theorem cutoff_liftDensity_L1_bound {T C : ℝ} {f : (ℝ × Position) × Velocity → ℝ}
    {w : Published.KineticPhase → ℝ} (hf : Measurable f) (hw : Measurable w)
    (hb : ∀ z, |w z| ≤ C) (hs : ∀ z, z ∉ region T → w z = 0) :
    eLpNorm (fun z => w z*liftDensity f z) 1 volume ≤
      ENNReal.ofReal C*eLpNorm f 1 ((AnnularEnvelope.timePositionVolume T).prod volume) := by
  have he : (fun z => w z*liftDensity f z) = (region T).indicator (fun z => w z*liftDensity f z) := by
    funext z
    by_cases hz : z ∈ region T
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz,hs z hz,zero_mul]
  rw [he,eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_region T),← cellVolume_eq T]
  calc
    _ ≤ ENNReal.ofReal C*eLpNorm (liftDensity f) 1 (cellVolume T) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hw.mul (liftDensity_measurable hf)).aestronglyMeasurable
      filter_upwards [] with z
      change ‖w z*liftDensity f z‖ ≤ C*‖liftDensity f z‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb z) (norm_nonneg _)
    _ = _ := by rw [eLpNorm_liftDensity hf]

theorem cutoff_liftDensity_integrable {T C : ℝ} {f : (ℝ × Position) × Velocity → ℝ}
    {w : Published.KineticPhase → ℝ} (hf : Measurable f) (hw : Measurable w)
    (hfi : Integrable f ((AnnularEnvelope.timePositionVolume T).prod volume))
    (hb : ∀ z, |w z| ≤ C) (hs : ∀ z, z ∉ region T → w z = 0) :
    Integrable (fun z => w z*liftDensity f z) := by
  apply memLp_one_iff_integrable.mp
  exact (cutoff_liftDensity_L1_bound hf hw hb hs).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_one_iff_integrable.mpr hfi))

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Weak limits and uniform integrability along flight with a fixed velocity restriction -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.TorusFlight

theorem flight_snd (t : ℝ) (p : Phase) : (flight t p).2 = p.2 := rfl

theorem backRegroup_measurePreserving (μ : Measure ℝ) (ν : Measure Velocity)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun z : (ℝ × Position) × Velocity =>
      (z.1.1,flight (-z.1.1) (z.1.2,z.2)))
      ((μ.prod volume).prod ν) (μ.prod ((volume : Measure Position).prod ν)) := by
  have hb : MeasurePreserving (fun z : ℝ × Phase => (z.1,flight (-z.1) z.2))
      (μ.prod ((volume : Measure Position).prod ν))
      (μ.prod ((volume : Measure Position).prod ν)) :=
    (MeasurePreserving.id μ).skew_product (g := fun (t : ℝ) (p : Phase) => flight (-t) p)
      (measurable_flight.comp (measurable_fst.neg.prodMk measurable_snd))
      (ae_of_all _ (fun t => (flight_measurePreserving_velocity (-t) ν).map_eq))
  exact hb.comp (measurePreserving_prodAssoc μ (volume : Measure Position) ν)

theorem weak_along_regroup_local {μ : Measure ℝ} {ν : Measure Velocity}
    [SFinite μ] [SFinite ν]
    {f : ℕ → (ℝ × Position) × Velocity → ℝ} {g : (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (hw : Published.WeakL1Converges ((μ.prod volume).prod ν) f g) :
    Published.WeakL1Converges (μ.prod ((volume : Measure Position).prod ν))
      (fun n => along (regroup (f n))) (along (regroup g)) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (backRegroup_measurePreserving μ ν)
    (fun n => (hfm n).comp (alongRegroup_measurePreserving μ ν).measurable)
    (hw.1.comp (alongRegroup_measurePreserving μ ν).measurable)
  simpa only [along,regroup,Function.comp_def,neg_flight,flight_snd] using hw

theorem uniformIntegrable_along_regroup_local {μ : Measure ℝ} {ν : Measure Velocity}
    [SFinite μ] [SFinite ν] {f : ℕ → (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hu : UniformIntegrable f 1 ((μ.prod volume).prod ν)) :
    UniformIntegrable (fun n => along (regroup (f n))) 1
      (μ.prod ((volume : Measure Position).prod ν)) := by
  apply Compactness.uniformIntegrable_of_comp_measurePreserving (backRegroup_measurePreserving μ ν)
    (fun n => (hfm n).comp (alongRegroup_measurePreserving μ ν).measurable)
  simpa only [along,regroup,Function.comp_def,neg_flight,flight_snd] using hu

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Localized torus velocity averages obey their exact L1 error bound -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.TorusKineticChart

theorem average_lift_difference_le {T C : ℝ}
    {f g : (ℝ × Position) × Velocity → ℝ} {w : Published.KineticPhase → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hwm : Measurable w)
    (hfi : Integrable f ((AnnularEnvelope.timePositionVolume T).prod volume))
    (hgi : Integrable g ((AnnularEnvelope.timePositionVolume T).prod volume))
    (hb : ∀ z, |w z| ≤ C) (hs : ∀ z, z ∉ region T → w z = 0) :
    eLpNorm (fun z => (∫ v, w (z,v)*liftDensity f (z,v))-
      (∫ v, w (z,v)*liftDensity g (z,v))) 1 volume ≤
      ENNReal.ofReal C*eLpNorm (f-g) 1 ((AnnularEnvelope.timePositionVolume T).prod volume) := by
  have hif := cutoff_liftDensity_integrable hfm hwm hfi hb hs
  have hig := cutoff_liftDensity_integrable hgm hwm hgi hb hs
  have he : (fun z => (∫ v, w (z,v)*liftDensity f (z,v))-
      (∫ v, w (z,v)*liftDensity g (z,v))) =ᵐ[volume]
      (fun z => ∫ v, w (z,v)*liftDensity (f-g) (z,v)) := by
    filter_upwards [hif.prod_right_ae,hig.prod_right_ae] with z hf hg
    rw [← integral_sub hf hg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun v => by
      change w (z,v)*liftDensity f (z,v)-w (z,v)*liftDensity g (z,v) =
        w (z,v)*(liftDensity f (z,v)-liftDensity g (z,v))
      ring)
  rw [eLpNorm_congr_ae he]
  exact (Compactness.eLpNorm_integral_le (hwm.mul (liftDensity_measurable (hfm.sub hgm)))).trans
    (cutoff_liftDensity_L1_bound (hfm.sub hgm) hwm hb hs)

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Removing velocity windows from time-phase null-set statements -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness
variable {μ : Measure ℝ} [SFinite μ]

theorem ae_timePhase_of_velocity_windows {P : ℝ × Phase → Prop}
    (h : ∀ n : ℕ, ∀ᵐ z ∂μ.prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ)))), P z) :
    ∀ᵐ z ∂μ.prod (volume : Measure Phase), P z := by
  have hg : ∀ n : ℕ, ∀ᵐ z ∂(μ.prod (volume : Measure Position)).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ))),
      P (z.1.1,(z.1.2,z.2)) := fun n =>
    (measurePreserving_prodAssoc μ (volume : Measure Position)
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ)))).quasiMeasurePreserving.ae (h n)
  have hh := ae_prod_of_velocity_windows hg
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure Velocity)).symm.quasiMeasurePreserving.ae hh

end BoltzmannNonuniqueness

end

end

end OAI
