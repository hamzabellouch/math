import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

namespace OAI

/-! The graph of spatial differentiation in the uniform norm is closed.

Both the function and its proposed derivative are bounded continuous maps. This
is the basic completeness lemma for finite families of bounded spatial jets.
-/

noncomputable section
namespace ForcedComputation

open Filter
open scoped Topology BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform limits of a function and its derivative remain a derivative pair. -/
theorem isClosed_boundedDerivativeGraph :
    IsClosed {p : (E →ᵇ F) × (E →ᵇ (E →L[ℝ] F)) |
      ∀ x, HasFDerivAt p.1 (p.2 x) x} := by
  apply IsSeqClosed.isClosed
  intro u p hu hp
  have h₀ : TendstoUniformly (fun n => (u n).1) p.1 atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (continuous_fst.tendsto p |>.comp hp)
  have h₁ : TendstoUniformly (fun n => (u n).2) p.2 atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (continuous_snd.tendsto p |>.comp hp)
  exact fun x => hasFDerivAt_of_tendstoUniformly h₁
    (fun n y => hu n y) (fun y => h₀.tendsto_at y) x

/-- The bounded derivative graph, with its inherited uniform product norm. -/
def boundedDerivativeGraph :
    ClosedSubmodule ℝ ((E →ᵇ F) × (E →ᵇ (E →L[ℝ] F))) where
  carrier := {p | ∀ x, HasFDerivAt p.1 (p.2 x) x}
  zero_mem' := by
    intro x
    change HasFDerivAt (fun _ : E => (0 : F)) (0 : E →L[ℝ] F) x
    exact hasFDerivAt_const (𝕜 := ℝ) (0 : F) x
  add_mem' := by
    intro p q hp hq x
    exact (hp x).add (hq x)
  smul_mem' := by
    intro c p hp x
    exact (hp x).const_smul c
  isClosed' := isClosed_boundedDerivativeGraph E F

@[simp] theorem mem_boundedDerivativeGraph
    (p : (E →ᵇ F) × (E →ᵇ (E →L[ℝ] F))) :
    p ∈ boundedDerivativeGraph E F ↔ ∀ x, HasFDerivAt p.1 (p.2 x) x := Iff.rfl

/-- A bounded function with bounded continuous derivative, in its graph norm. -/
abbrev BoundedC1 := boundedDerivativeGraph E F

instance [CompleteSpace F] : CompleteSpace (BoundedC1 E F) := inferInstance

end ForcedComputation

end

end OAI
