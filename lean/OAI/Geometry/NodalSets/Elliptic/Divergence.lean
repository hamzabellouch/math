import OAI.Geometry.NodalSets.Elliptic.WeightedDivergenceInvariance

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def referenceWeightedOperator (v rho : Coord → ℝ)
    (A : Fin 4 → Fin 4 → Coord → ℝ) (u : Coord → ℂ) (x : Coord) : ℂ :=
  (rho x : ℂ)⁻¹ * ((v x : ℂ)⁻¹ * complexDivergence
    (fun i z ↦ ∑ j, ((v z : ℂ) * (A i j z : ℂ)) * coordPartial j u z) x)

theorem sourceWeightedOperator_reference
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (v rho : Coord → ℝ) (u : Coord → ℂ) (x : Coord) :
    sourceWeightedOperator g (fun z ↦ rho z * v z) u x =
      referenceWeightedOperator v rho (fun i j z ↦ rho z * sourcePrincipal g i j z) u x := by
  have he : sourceFlux g (fun z ↦ rho z * v z) u =
      (fun i z ↦ ∑ j, ((v z : ℂ) * ((rho z * sourcePrincipal g i j z : ℝ) : ℂ)) *
        coordPartial j u z) := by
    funext i z
    unfold sourceFlux
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  unfold sourceWeightedOperator referenceWeightedOperator
  rw [he]
  push_cast
  ring

end
end Yau.Geometry

end OAI
