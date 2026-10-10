import OAI.MathematicalPhysics.Boltzmann.Approximation.DormantConstruction
import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedCollisionIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative

namespace OAI

section

/-! # Kinetic collision integrability in physical admissibility coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
open CollisionCompactness

theorem kinetic_collision_conditions {F : Evolution} {T : ℝ}
    (h : let g := kineticDensity F
      let μ := (volume.restrict (Icc 0 T)).prod (volume : Measure Position)
      Integrable (fun p => gainDensity g p/(1+g p/maxwellian p.2)) (μ.prod volume) ∧
      Integrable (fun p => lossDensity g p/(1+g p/maxwellian p.2)) (μ.prod volume) ∧
      ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
        Integrable (fun q => postRate g (collisionGrouping.symm (p,q)))
          ((volume : Measure Velocity).prod sphereArea) ∧
        Integrable (fun q => preRate g (collisionGrouping.symm (p,q)))
          ((volume : Measure Velocity).prod sphereArea)) :
    IntegrableOn (fun z : ℝ × Phase => gain (F z.1) z.2.1 z.2.2 /
      (1+relativeDensity F z.1 z.2)) (boundedTimes T) ∧
    IntegrableOn (fun z : ℝ × Phase => loss (F z.1) z.2.1 z.2.2 /
      (1+relativeDensity F z.1 z.2)) (boundedTimes T) ∧
    ∀ᵐ z ∂volume.restrict (boundedTimes T),
      Integrable (fun q : Velocity × Sphere => collisionKernel z.2.2 q.1 q.2 *
        F z.1 (z.2.1,scatterLeft z.2.2 q.1 q.2)*F z.1 (z.2.1,scatterRight z.2.2 q.1 q.2))
          ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere => collisionKernel z.2.2 q.1 q.2 *
        F z.1 z.2*F z.1 (z.2.1,q.1)) ((volume : Measure Velocity).prod sphereArea) := by
  have hg := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable h.1
  have hl := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable h.2.1
  have hfib := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.quasiMeasurePreserving.ae h.2.2
  constructor
  · change Integrable _ (volume.restrict (boundedTimes T))
    rw [← phaseInterval_measure]
    apply hg.congr
    apply ae_of_all
    intro z
    change gainDensity (kineticDensity F) ((z.1,z.2.1),z.2.2)/(1+F z.1 z.2/maxwellian z.2.2) = _
    rw [show gainDensity (kineticDensity F) ((z.1,z.2.1),z.2.2) = gain (F z.1) z.2.1 z.2.2 from kineticDensity_gain F z]
    rfl
  constructor
  · change Integrable _ (volume.restrict (boundedTimes T))
    rw [← phaseInterval_measure]
    exact hl
  · rw [← phaseInterval_measure]
    filter_upwards [hfib] with z hz
    constructor
    · convert hz.1 using 1
      funext q
      exact (postRate_formula (kineticDensity F) (collisionGrouping.symm (((z.1,z.2.1),z.2.2),q))).symm
    · exact hz.2

end BoltzmannNonuniqueness

end

end

section

/-! # The four-dimensional Jacobian of kinetic time-space dilation -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace BoltzmannNonuniqueness.JetCopyDatum

def kineticDilationEquiv (r : ℝ) (hr : r ≠ 0) :
    Published.KineticPhase ≃ᵐ Published.KineticPhase :=
  (Homeomorph.smul (Units.mk0 r hr) : (ℝ × Velocity) ≃ₜ (ℝ × Velocity)).toMeasurableEquiv.prodCongr
    (MeasurableEquiv.refl Velocity)

theorem kineticDilationEquiv_apply {r : ℝ} (hr : r ≠ 0) (z : Published.KineticPhase) :
    kineticDilationEquiv r hr z = kineticDilation r z := rfl

theorem kineticDilation_map {r : ℝ} (hr : 0 < r) :
    Measure.map (kineticDilation r) volume = ENNReal.ofReal ((r^4)⁻¹) • volume := by
  have ht : Measure.map (fun t : ℝ => r*t) volume =
      ENNReal.ofReal r⁻¹ • (volume : Measure ℝ) := by
    simpa only [Module.finrank_self,pow_one,smul_eq_mul,abs_of_pos (inv_pos.mpr hr)] using
      Measure.map_addHaar_smul (volume : Measure ℝ) hr.ne'
  have hx : Measure.map (fun x : Velocity => r • x) volume =
      ENNReal.ofReal ((r^3)⁻¹) • (volume : Measure Velocity) := by
    have hdim : Module.finrank ℝ Velocity = 3 := by simp [Velocity]
    simpa only [hdim,abs_of_pos (inv_pos.mpr (pow_pos hr 3))] using
      Measure.map_addHaar_smul (volume : Measure Velocity) hr.ne'
  change Measure.map (Prod.map (Prod.map (fun t : ℝ => r*t) (fun x : Velocity => r • x)) id)
    (((volume : Measure ℝ).prod (volume : Measure Velocity)).prod (volume : Measure Velocity)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),ht,hx,Measure.map_id,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.prod_smul_left]
  have hc : ENNReal.ofReal r⁻¹ * ENNReal.ofReal ((r^3)⁻¹) = ENNReal.ofReal ((r^4)⁻¹) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    congr 1
    field_simp
  rw [hc]
  rfl

theorem kineticDilation_integral {r : ℝ} (hr : 0 < r) (f : Published.KineticPhase → ℝ) :
    (∫ z, f (kineticDilation r z)) = (r^4)⁻¹ * ∫ z, f z := by
  have h := (integral_map_equiv (μ := volume) (kineticDilationEquiv r hr.ne') f).symm
  change (∫ z, f (kineticDilation r z)) =
    ∫ z, f z ∂Measure.map (kineticDilation r) volume at h
  rw [kineticDilation_map hr,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le 4)),smul_eq_mul] at h
  exact h

theorem kineticDilation_inverse {r : ℝ} (hr : r ≠ 0) (z : Published.KineticPhase) :
    kineticDilation r⁻¹ (kineticDilation r z) = z := by
  ext <;> simp [kineticDilation,smul_smul,hr]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Bounded measurable tests for a fixed kinetic dilation -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem scaled_setIntegral {r : ℝ} (hr : 0 < r)
    {s : Set Published.KineticPhase} (hs : MeasurableSet s) (f : Published.KineticPhase → ℝ) :
    (∫ z in s, r⁻¹*f (kineticDilation r z)) =
      (r^5)⁻¹ * ∫ z in kineticDilation r⁻¹ ⁻¹' s, f z := by
  have hp : s.indicator (fun z => f (kineticDilation r z)) =
      fun z => ((kineticDilation r⁻¹ ⁻¹' s).indicator f) (kineticDilation r z) := by
    funext z
    by_cases hz : z ∈ s <;> simp [hz,kineticDilation_inverse hr.ne']
  rw [integral_const_mul,← integral_indicator hs,hp,kineticDilation_integral hr,
    integral_indicator (hs.preimage (kineticDilation_quasiMeasurePreserving (inv_pos.mpr hr)).measurable)]
  field_simp

theorem weak_scaled_setIntegral {r T : ℝ} (hr : 0 < r)
    {s : Set Published.KineticPhase} (hs : MeasurableSet s)
    (hc : kineticDilation r⁻¹ ⁻¹' s ⊆ TorusKineticChart.region T)
    {f : ℕ → Published.KineticPhase → ℝ} {g : Published.KineticPhase → ℝ}
    (h : Published.WeakL1Converges (TorusKineticChart.cellVolume T) f g) :
    Tendsto (fun n => ∫ z in s, r⁻¹*f n (kineticDilation r z)) atTop
      (𝓝 (∫ z in s, r⁻¹*g (kineticDilation r z))) := by
  let u := kineticDilation r⁻¹ ⁻¹' s
  have hu : MeasurableSet u := hs.preimage
    (kineticDilation_quasiMeasurePreserving (inv_pos.mpr hr)).measurable
  have hw := h.restrict hu
  rw [TorusKineticChart.cellVolume_eq,
    Measure.restrict_restrict_of_subset hc] at hw
  have ht := hw.2.2 (fun _ => 1) measurable_const ⟨1,by simp⟩
  simp only [one_mul] at ht
  simpa only [scaled_setIntegral hr hs] using ht.const_mul ((r^5)⁻¹)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
