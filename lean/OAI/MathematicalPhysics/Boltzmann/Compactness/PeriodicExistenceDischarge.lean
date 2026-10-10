import OAI.MathematicalPhysics.Boltzmann.Branching.AdmissibleDatumCongruence
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDilationIntegral
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGlobalRenormalized

namespace OAI

section

/-! # Global admissibility of the actual constructed periodic solution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_admissible
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    AdmissibleGlobal f (physicalEvolution f G.weakLimit.kineticProfile) := by
  refine {
    datum := ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩
    spacetime_measurable := (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).aestronglyMeasurable
    finite_each_time := fun _ ht => G.physical_finiteEntropy hf hi ht
    initial := ae_of_all _ (physicalEvolution_initial hf G.weakLimit.kineticProfile)
    weak_continuity := fun _ hψ hb => G.physical_weak_continuity hf hi hψ hb
    uniform_moment := fun _ _ => ⟨physicalEntropyBudget f,fun _ ht => G.physical_entropyMoment_le hf hi ht.1⟩
    collision_fibers := fun _ hT => (kinetic_collision_conditions (G.physical_kinetic_collision_integrability hf hi hT)).2.2
    gain_integrable := fun _ hT => (kinetic_collision_conditions (G.physical_kinetic_collision_integrability hf hi hT)).1
    loss_integrable := fun _ hT => (kinetic_collision_conditions (G.physical_kinetic_collision_integrability hf hi hT)).2.1
    renormalized_integrable := fun β φ => (G.physical_global_renormalized hf hi β φ).1
    renormalized_equation := fun β φ => (G.physical_global_renormalized hf hi β φ).2
    local_mass_integrable := fun φ => (G.physical_global_mass hf hi φ).1
    local_mass := fun φ => (G.physical_global_mass hf hi φ).2
    momentum_conservation := fun _ ht => G.physical_momentum_conservation hf hi ht
    energy_inequality := fun _ ht => G.physical_energy_le hf hi ht
    entropy_inequality := fun _ ht => G.physical_entropy_dissipation hf hi ht
  }

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Periodic global existence in the full admissibility class

The proof constructs finite cutoff solutions, extracts their common density and collision
limit, proves nonlinear characteristic closure, and constructs admissible traces at every time.
-/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness
open PeriodicApproximation

theorem periodicExistenceInput : PeriodicExistenceInput := by
  intro f hf
  let g : Density := fun p => max 0 (hf.2.1.mk f p)
  have hgm : Measurable g := measurable_const.max hf.2.1.stronglyMeasurable_mk.measurable
  have hgn (p : Phase) : 0 ≤ g p := le_max_left _ _
  have he : f =ᵐ[volume] g := by
    filter_upwards [hf.1,hf.2.1.ae_eq_mk] with p hp he
    change f p = max 0 (hf.2.1.mk f p)
    rw [← he,max_eq_right hp]
  have hgi : Integrable (entropyMoment g) := hf.2.2.congr
    (he.mono (fun p hp => by unfold entropyMoment; rw [hp]))
  obtain ⟨G⟩ := exists_globalCollisionLimit g hgm hgn hgi
  exact ⟨physicalEvolution g G.weakLimit.kineticProfile,
    (G.physical_admissible hgn hgi).congr_datum hf he.symm⟩

end BoltzmannNonuniqueness

end

end

end OAI
