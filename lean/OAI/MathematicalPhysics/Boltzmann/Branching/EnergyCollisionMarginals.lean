import OAI.MathematicalPhysics.Boltzmann.Branching.ExponentialPairIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityPolynomialBounds
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalAdmissibility

namespace OAI

section

/-! # Both collision rates are integrable with the energy weight -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem preRate_energy_integrable {μ : Measure X} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun z => ‖z.1.2.1‖^2*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hd := (hi.const_mul 7).comp_fst sphereArea
  apply hd.mono' (by
    exact ((measurable_fst.snd.fst.norm.pow_const 2).mul (preRate_measurable hfm)).aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (preRate_nonneg hfn z))]
  calc
    _ = (‖z.1.2.1‖^2*collisionKernel z.1.2.1 z.1.2.2 z.2)*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) := by
      unfold preRate
      ring
    _ ≤ (7*VelocityMoment.weight z.1.2.1*VelocityMoment.weight z.1.2.2)*
        f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (VelocityMoment.norm_sq_kernel_le_weight _ _ _) (hfn _)) (hfn _)
    _ = _ := by unfold exponentialPair; ring

theorem preRate_other_energy_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun z => ‖z.1.2.2‖^2*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable
    (preRate_energy_integrable hfm hfn hi)
  simp only [Function.comp_def,preRate_particleSwap] at h
  exact h

theorem postRate_energy_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun z => ‖z.1.2.1‖^2*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hs := (preRate_energy_integrable hfm hfn hi).add (preRate_other_energy_integrable hfm hfn hi)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2*preRate f z) := by
    apply Measurable.mul _ (preRate_measurable hfm)
    unfold scatterLeft normalComponent
    fun_prop
  have hl : Integrable (fun z => ‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    apply hs.mono' hm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (preRate_nonneg hfn z))]
    have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
    have he := scatter_energy z.1.2.1 z.1.2.2 z.2 hw
    have hle : ‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2 ≤ ‖z.1.2.1‖^2+‖z.1.2.2‖^2 := by
      nlinarith [sq_nonneg ‖scatterRight z.1.2.1 z.1.2.2 z.2‖]
    exact (mul_le_mul_of_nonneg_right hle (preRate_nonneg hfn z)).trans_eq (by
      exact add_mul _ _ _)
  have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hl
  have he : (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ‖scatterLeft (scatterTriple z).1.2.1 (scatterTriple z).1.2.2 (scatterTriple z).2‖^2*
        preRate f (scatterTriple z)) = (fun z => ‖z.1.2.1‖^2*postRate f z) := by
    funext z
    have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
    change ‖scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2‖^2*preRate f (scatterTriple z) = _
    rw [scatterLeft_involutive _ _ _ hw]
    rfl
  change Integrable (fun z => ‖scatterLeft (scatterTriple z).1.2.1
    (scatterTriple z).1.2.2 (scatterTriple z).2‖^2*preRate f (scatterTriple z)) _ at h
  rw [he] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Energy-weighted gain and loss integrability for the local solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem gainLoss_energy_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun p => ‖p.2‖^2*gainDensity f p) (μ.prod volume) ∧
      Integrable (fun p => ‖p.2‖^2*lossDensity f p) (μ.prod volume) := by
  exact ⟨(collision_test_marginal (postRate f) (fun p => ‖p.2‖^2)
      (postRate_energy_integrable hfm hfn hi)).1,
    (collision_test_marginal (preRate f) (fun p => ‖p.2‖^2)
      (preRate_energy_integrable hfm hfn hi)).1⟩

end CollisionCompactness

namespace LocalMildSolution

theorem energy_gainLoss_integrable {T : ℝ} {f₀ : Density} {F : Evolution}
    (S : LocalMildSolution T f₀ F) {M : ℝ × Position → ℝ}
    (hMn : ∀ u, 0 ≤ M u)
    (hMsq : Integrable (fun u => (M u)^2) (AnnularEnvelope.timePositionVolume T))
    (hbound : ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T,
      VelocityMoment.moment (fun v => F u.1 (u.2,v)) ≤ ENNReal.ofReal (M u)) :
    IntegrableOn (fun p : ℝ × Phase => ‖p.2.2‖^2*gain (F p.1) p.2.1 p.2.2) (boundedTimes T) ∧
    IntegrableOn (fun p : ℝ × Phase => ‖p.2.2‖^2*loss (F p.1) p.2.1 p.2.2) (boundedTimes T) := by
  have hm : Measurable (kineticDensity F) := S.measurable.comp MeasurableEquiv.prodAssoc.measurable
  have hn : ∀ p, 0 ≤ kineticDensity F p := fun p => S.nonnegative _ _
  have hi := CollisionCompactness.exponentialPair_integrable hm hn hMn hMsq hbound
  have hterms := CollisionCompactness.gainLoss_energy_integrable hm hn hi
  have hg := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hterms.1
  have hl := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hterms.2
  have he : ((fun p => ‖p.2‖^2*CollisionCompactness.gainDensity (kineticDensity F) p) ∘
      MeasurableEquiv.prodAssoc.symm) = (fun p : ℝ × Phase => ‖p.2.2‖^2*gain (F p.1) p.2.1 p.2.2) := by
    funext p
    exact congrArg (fun a => ‖p.2.2‖^2*a) (kineticDensity_gain F p)
  rw [he] at hg
  change Integrable _ _ ∧ Integrable _ _
  rw [← phaseInterval_measure]
  exact ⟨hg,hl⟩

end LocalMildSolution
end BoltzmannNonuniqueness

end

end

end OAI
