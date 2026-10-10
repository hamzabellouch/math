import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FixedParticleAnalytic
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowEffective
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowTail

namespace OAI

/-! Full main theorem of A Fixed Particle Test for Computation in a Forced
Viscous Flow, including the terminating evaluator and machine-only tail. -/

namespace ForcedComputation
open ShearFlows Recorder

def fixedParticleProgram (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    Input × Input :=
  (shiftedLoader fixedStart (initialPointQ I hI) 0, recorderInputAtHeight I.1 hI.1 0)

theorem fixedParticleLoader_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (fixedParticleProgram I hI).1 :=
  shiftedLoader_valid _ _ _ (by intro j; fin_cases j <;> norm_num [fixedStart])
    (initialPointQ_bounds I hI)

theorem fixedParticleBody_valid (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : ValidInput (fixedParticleProgram I hI).2 :=
  recorderInputAtHeight_valid I.1 (Alternating.ValidInput.machine_wellFormed hI) 0

noncomputable def fixedParticleForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := force ν (fixedParticleVelocity I hI)

theorem fixed_particle_effective_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    SlowFluidProperties 1 ν (fixedParticleVelocity I hI) ∧
    (∀ t x, Real.exp 1 - 1 ≤ t →
      fixedParticleVelocity I hI (t, x) =
        slowVelocity (recorderInputAtHeight I.1 hI.1 0).realizingVelocity (t, x) ∧
      fixedParticleForce ν I hI (t, x) =
        force ν (slowVelocity (recorderInputAtHeight I.1 hI.1 0).realizingVelocity) (t, x)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (y : SpaceTime)
      (ha : IsFastRealName a ν) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε),
      ‖mixedDerivative (fixedParticleForce ν I hI) α y -
        rationalVector (evaluateSlowForce (fixedParticleProgram I hI).1
          (fixedParticleProgram I hI).2 (fixedParticleLoader_valid I hI)
          (fixedParticleBody_valid I hI) α a ha b hb ε hε)‖ ≤ (ε : ℝ)) ∧
    ∃ Ψ : ℝ → Space → Space, IsMaterialFlow 1 (fixedParticleVelocity I hI) Ψ ∧
      (Alternating.Halts I ↔ ∃ t : ℝ, 0 ≤ t ∧
        1 / 2 < Ψ t ![1 / 8, 3 / 8, 0] 0 ∧ Ψ t ![1 / 8, 3 / 8, 0] 0 < 1) := by
  obtain ⟨hp, he⟩ := fixed_particle_analytic_computation I hI ν hν
  refine ⟨hp, ?_, ?_, he⟩
  · intro t x ht
    exact slow_initialized_tail _ _ ν ht x
  · intro α a b y ha hb ε hε
    exact evaluateSlowForce_spec (fixedParticleLoader_valid I hI)
      (fixedParticleBody_valid I hI) α a ha b hb ε hε

end ForcedComputation

end OAI
