import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulse

namespace OAI

/-! Divergence commutes with the finite arrays used by the prescribed
whole-plane drift. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian
open ShearFlows
open scoped ContDiff BigOperators

theorem divergence_finite_sum {ι : Type*} (s : Finset ι) (V : ι → Plane → Plane)
    (hV : ∀ i ∈ s, ContDiff ℝ ∞ (V i)) (x : Plane) :
    divergence (fun y => ∑ i ∈ s, V i y) x = ∑ i ∈ s, divergence (V i) x := by
  have he (j : Fin 2) : spatialD j (fun y => (∑ i ∈ s, V i y) j) x =
      ∑ i ∈ s, spatialD j (fun y => V i y j) x := by
    have hf : (fun y : Plane => (∑ i ∈ s, V i y) j) =
        (fun y => ∑ i ∈ s, V i y j) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hf]
    unfold spatialD
    have hVi (i : ι) (hi : i ∈ s) : DifferentiableAt ℝ (fun y => V i y j) x :=
      ((contDiff_apply ℝ ℝ j).comp (hV i hi)).differentiable (by simp) x
    rw [fderiv_fun_sum hVi]
    simp only [sum_apply]
  unfold divergence
  simp_rw [he]
  exact Finset.sum_comm

end ForcedComputation.PlanarHamiltonian

end

end OAI
