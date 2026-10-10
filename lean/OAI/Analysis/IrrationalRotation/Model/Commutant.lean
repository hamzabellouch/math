import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

namespace OAI

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def operatorCommutant (T : H →L[ℂ] H) : Subalgebra ℂ (H →L[ℂ] H) :=
  Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))

def IsInvariant (T : H →L[ℂ] H) (L : Submodule ℂ H) : Prop :=
  ∀ x ∈ L, T x ∈ L

def IsHyperinvariant (T : H →L[ℂ] H) (L : Submodule ℂ H) : Prop :=
  IsClosed (L : Set H) ∧ ∀ A ∈ operatorCommutant T, IsInvariant A L

def IsTransitive (A : Subalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∀ L : Submodule ℂ H, IsClosed (L : Set H) →
    (∀ B ∈ A, IsInvariant B L) → L = ⊥ ∨ L = ⊤

def HasNoNontrivialHyperinvariantSubspace (T : H →L[ℂ] H) : Prop :=
  ∀ L : Submodule ℂ H, IsHyperinvariant T L → L = ⊥ ∨ L = ⊤

noncomputable def strongOperatorUnderlying (B : H →Lₚₜ[ℂ] H) : H →L[ℂ] H :=
  (UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite}).symm B

def IsStronglyClosed (A : Subalgebra ℂ (H →L[ℂ] H)) : Prop :=
  IsClosed {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ A}

end Invariant233

end OAI
