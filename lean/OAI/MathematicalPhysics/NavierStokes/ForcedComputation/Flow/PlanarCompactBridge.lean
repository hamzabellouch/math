import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarProcessor
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedPlanarProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPerturbations

namespace OAI

/-! Agreement of the compact planar field with the finite periodic scalar
expression on the open unit-square chart, at every phase. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set

theorem periodic_eq_of_eqOn_unit {E : Type*} {f g : ℝ → E}
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (he : EqOn f g (Icc (0 : ℝ) 1)) : f = g := by
  funext t
  have hf' : f (Int.fract t) = f t := by
    simpa only [Int.fract, mul_one] using hf.sub_int_mul_eq (x := t) ⌊t⌋
  have hg' : g (Int.fract t) = g t := by
    simpa only [Int.fract, mul_one] using hg.sub_int_mul_eq (x := t) ⌊t⌋
  exact hf'.symm.trans ((he ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩).trans hg')

theorem planarSlice_periodic {H : FieldExpr}
    (hP : CubePeriodic 1 (SpatialExpression.spatialValue H)) (x : Plane) :
    Function.Periodic (fun s => planarSlice H s x) 1 := by
  intro s
  have he : (fun Y => SpatialExpression.spatialValue H (atHeight Y (s + 1))) =
      (fun Y => SpatialExpression.spatialValue H (atHeight Y s)) := by
    funext Y
    have hv : atHeight Y (s + 1) = atHeight Y s + latticeVector 1 ![0, 0, 1] := by
      ext j
      fin_cases j <;> simp [atHeight, latticeVector]
    rw [hv]
    exact hP _ _
  change PlanarHamiltonian.field _ x = PlanarHamiltonian.field _ x
  rw [he]

namespace Recorder.Planar
open PlanarHamiltonian

theorem normalized_planar_field_on_chart (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) (x : Plane)
    (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    PlanarHamiltonian.periodicVelocity (normalizedPulse I hI) s x =
      planarSlice (normalizedHamiltonian I hI) s x := by
  have he : (fun t => PlanarHamiltonian.periodicVelocity (normalizedPulse I hI) t x) =
      (fun t => planarSlice (normalizedHamiltonian I hI) t x) := by
    apply periodic_eq_of_eqOn_unit (PlanarHamiltonian.periodicVelocity_periodic _ x)
      (planarSlice_periodic (normalizedHamiltonian_periodic I hI) x)
    intro t ht
    exact (PlanarHamiltonian.periodicVelocity_on_unit (normalizedPulse_valid I hI)
      (normalizedPulse_inUnit I hI) ht x).trans
        (processorExpression_planar_field (normalizedPulse_valid I hI)
          (normalizedPulse_inUnit I hI) ht hx₀ hx₁).symm
  exact congrFun he s

end Recorder.Planar
end ForcedComputation

end

end OAI
