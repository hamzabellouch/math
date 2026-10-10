import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeCorollaryGeometry
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeEffective

namespace OAI

/-! The rapid-torus corollary with its stated fixed particle and observation
slab. The construction is a rational transverse change of the proved lattice
program; in particular no Poisson existence or computation assumption is used. -/

noncomputable section
open Set
open scoped ContDiff
namespace PeriodicLattice.RapidTorus
open TorusCalculus Quantitative EffectiveFields

def IsCorollaryParticle (U : VectorField) (X : ℝ → Space) : Prop :=
  X 0 = corollaryStart ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt X (U t (torusMk (X t))) (Ici 0) t

def CorollaryConclusion (ν : ℝ) (d : Input) (U f : VectorField) (p : ScalarField)
    (C : ℕ → MultiIndex → ℕ → ℕ) : Prop :=
  Smooth U ∧ Smooth f ∧ Smooth p ∧
  MeanZero U ∧ MeanZero f ∧ MeanZero p ∧ Solenoidal f ∧
  ClassicalSolution ν f U p ∧ UniqueClassical ν f U p ∧
  RapidPair U f C ∧
  ∃ X : ℝ → Space, IsCorollaryParticle U X ∧
    (∀ Y : ℝ → Space, IsCorollaryParticle U Y →
      ∀ t : ℝ, 0 ≤ t → Y t = X t) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ torusMk (X t) ∈ corollaryDetector) ↔ Halts d)

/-- Corollary `cor:rapid-torus` of paper 379-06: the exact fixed label is
`(1/2,1/4,1/2)` and the open observation slab is `1/4 < x₀ < 3/8`.
Both the velocity and solenoidal force have terminating evaluators and
computable bounds for every mixed derivative and every polynomial decay rate. -/
theorem solenoidal_rapid_torus (ν : ℝ) (hν : 0 < ν) (hc : ComputableReal ν) :
    IsOpen corollaryDetector ∧
    ∃ (U f : Input → VectorField) (p : Input → ScalarField)
      (C : Input → ℕ → MultiIndex → ℕ → ℕ),
      UniformlyEffective U ∧ UniformlyEffective f ∧ EffectiveConstants C ∧
      ∀ d : Input, d.WellFormed → CorollaryConclusion ν d (U d) (f d) (p d) (C d) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖ν‖
  have he := CertifiedReal.computableReal_effective hc
  refine ⟨corollaryDetector_open,
    (fun d => transformedField (FluidLift.velocity d)),
    (fun d => transformedField (FluidLift.solenoidalForce ν d)),
    (fun d => -shiftedField (FluidLift.potential d)), corollaryConstants ν N hN,
    uniformlyEffective_of_certificate (transformedCertificate velocityCertificate)
      (componentsEffective_transformed velocity_effective),
    uniformlyEffective_of_certificate
      (transformedCertificate (solenoidalForceCertificate ν N hN))
      (componentsEffective_transformed (solenoidalForce_effective ν he)),
    corollaryConstants_effective ν N hN, fun d hd => ?_⟩
  have hu := transformedField_smooth (FluidLift.velocity_contDiff d)
  have hf := transformedField_smooth (FluidLift.solenoidalForce_contDiff ν d)
  have hp := (shiftedField_smooth (FluidLift.potential_contDiff d)).neg
  have hclass := transformed_classical_solution ν d
  refine ⟨hu.contDiffOn, hf.contDiffOn, hp.contDiffOn,
    transformedField_meanZero (FluidLift.velocity_contDiff d) (FluidLift.velocity_meanZero d),
    transformedField_meanZero (FluidLift.solenoidalForce_contDiff ν d)
      (FluidLift.solenoidalForce_meanZero ν d), hclass.pressureMeanZero,
    transformed_solenoidalForce ν d hd, hclass, classical_unique hν.le hclass,
    (corollaryConstants_bounds ν N hN d hd).2, corollaryPath d,
    ⟨corollaryPath_start d, fun t ht =>
      (corollaryPath_hasDerivAt d hd ht).hasDerivWithinAt⟩,
    fun Y hY t ht => corollaryPath_unique d hd hY.1 hY.2 ht,
    transformed_path_event d hd⟩

end PeriodicLattice.RapidTorus

end

end OAI
