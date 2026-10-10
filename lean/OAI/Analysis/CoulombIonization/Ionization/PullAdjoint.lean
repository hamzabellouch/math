import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Pull

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}
lemma pull_adjoint_symm (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν) (ψ : Lp ℂ 2 μ) :
    (pull e he).adjoint ψ = pull e.symm (he.symm e) ψ := by
  apply ext_inner_left ℂ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    _ = inner ℂ (pull e he φ) (pull e he (pull e.symm (he.symm e) ψ)) := by
      rw [pull_symm e he]
    _ = _ := pull_inner e he _ _
end CoulombPauli

end

end OAI
