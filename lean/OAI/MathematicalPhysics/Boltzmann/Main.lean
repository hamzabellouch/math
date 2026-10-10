import OAI.MathematicalPhysics.Boltzmann.UnconditionalMainProof

namespace OAI

/-! # Nonuniqueness for the periodic hard-sphere Boltzmann equation

The exact main statement includes two distinct global renormalized solutions of one
bounded-velocity initial datum, with local mass conservation, total momentum conservation, energy and
entropy-dissipation inequalities, and strong early L1 continuity with integrable collisions.
-/
namespace BoltzmannNonuniqueness

theorem nonuniqueness :
    ∃ f₀ : Density, BoundedVelocitySupport f₀ ∧
      ∃ (F G : Evolution) (T : ℝ), AdmissibleGlobal f₀ F ∧ AdmissibleGlobal f₀ G ∧
        StrongEarly T F ∧ StrongEarly T G ∧
        ∃ t ∈ Set.Icc 0 T, ¬(F t =ᵐ[MeasureTheory.volume] G t) :=
  nonuniqueness_proved

end BoltzmannNonuniqueness

end OAI
