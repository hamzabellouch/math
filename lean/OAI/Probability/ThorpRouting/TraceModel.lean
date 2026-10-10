import OAI.Probability.ThorpRouting.Harmonic.Main

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

noncomputable local instance hsNorm (μ : YoungDiagram) : NormedAddCommGroup (hilbertSpace μ) := inferInstance
noncomputable local instance hsInner (μ : YoungDiagram) : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
noncomputable local instance hsFinite (μ : YoungDiagram) : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance

noncomputable def Q (d : ℕ) (μ : Shapes (2^d)) :
    hilbertSpace μ.1 →L[ℂ] hilbertSpace μ.1 :=
  sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d d)

noncomputable def absoluteTrace {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) (P : ℝ) : ℝ :=
  (LinearMap.trace ℂ V (CFC.rpow (CFC.sqrt (star A * A)) P).toLinearMap).re

noncomputable def regularTrace (d : ℕ) (P : ℝ) : ℝ :=
  ∑ μ : Shapes (2^d), (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
    absoluteTrace (V := hilbertSpace μ.1) (Q d μ) P

noncomputable def sweepDistance (d v : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (1/2:ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d (v*d) (g*σ⁻¹) - 1/(Nat.factorial (2^d):ℝ)|

def MainStatement : Prop :=
  ∃ P : ℝ, 2 ≤ P ∧ ∀ d : ℕ, 1 ≤ d →
    regularTrace d P ≤ 1 + ((2 : ℝ)^d) ^ (-10 : ℤ) ∧
    ∀ v : ℤ, P ≤ 2 * (v : ℝ) → ∀ σ : Equiv.Perm (Card d),
      sweepDistance d v.toNat σ ≤ (1/2 : ℝ) * ((2 : ℝ)^d) ^ (-5 : ℤ)

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
