import Mathlib
import OAI.Analysis.Commutator.CycleInvariants
import OAI.Analysis.Commutator.MatrixClassification
import OAI.Analysis.Commutator.RectangularTensors

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {I K J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype K] [DecidableEq K] [Nonempty K] [Fintype J] [DecidableEq J]

theorem cycleTrace_map (φ : Matrix I I ℂ →ₐ[ℂ] Matrix K K ℂ)
    (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) :
    cycleTrace σ (fun j => φ (A j)) = cycleTrace σ A := by
  classical
  let o : I := Classical.choice ‹Nonempty I›
  let E := MatrixModules.corner (MatrixModules.matrixRepresentation φ) o
  let R := Fin (Module.finrank ℂ E)
  let b : Module.Basis R ℂ E := Module.finBasis ℂ E
  let : Nonempty R := MatrixModules.multiplicity_nonempty φ o b
  let X := MatrixModules.forwardMatrix φ o b
  let Y := MatrixModules.backwardMatrix φ o b
  have hYX : Y * X = 1 := MatrixModules.backward_forward φ o b
  have hA : (fun j => φ (A j)) = fun j => X * inflateMatrix (R := R) (A j) * Y := by
    funext j
    exact MatrixModules.classification φ o b (A j)
  have hr : rawCycleTrace σ (fun j => φ (A j)) =
      rawCycleTrace σ (fun j => inflateMatrix (R := R) (A j)) := by
    rw [hA]
    exact RectangularTensors.trace_transport X Y hYX _ σ
  have hc : Fintype.card K = Fintype.card (I × R) := by
    simpa only [Fintype.card_prod] using (MatrixModules.dimensions φ o b).symm
  calc
    _ = cycleTrace σ (fun j => inflateMatrix (R := R) (A j)) := by
      simp only [cycleTrace, hr, hc]
    _ = _ := cycleTrace_inflate R σ A

theorem stable_cycle_coefficients_map
    (φ : Matrix I I ℂ →ₐ[ℂ] Matrix K K ℂ)
    (b : J → I) (hb : Function.Injective b) (c d : Equiv.Perm J → ℂ)
    (h : ∀ A : J → Matrix I I ℂ,
      ∑ σ, c σ * cycleTrace σ A = ∑ σ, d σ * cycleTrace σ (fun j => φ (A j))) :
    c = d := by
  apply cycleTrace_coefficients_unique b hb c d
  intro A
  simpa only [cycleTrace_map] using h A

end Kadison.SchurWeyl
end

end OAI
