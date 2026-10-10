import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModel

namespace OAI

/-! Linear recovery of original signed tests from bounded retained tests
preserves the same circle model and zero complementary gradients. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem sphereFromPlaneFunction_linear_difference
    (u v : EuclideanPlane → ℝ) (a b : ℝ) (p : Sphere) :
    sphereFromPlaneFunction (fun x => a * u x - b * v x) p =
      a * sphereFromPlaneFunction u p - b * sphereFromPlaneFunction v p := by
  classical
  by_cases hp : p = OnePoint.infty <;> simp [sphereFromPlaneFunction, hp]

namespace CompactScalarCircleModel

 def linearDifference {G : Set Sphere} {n m : ℕ}
    {v : Fin n → EuclideanPlane → ℝ} (M : CompactScalarCircleModel G v)
    (left right : Fin m → Fin n) (a b : Fin m → ℝ) :
    CompactScalarCircleModel G
      (fun i x => a i * v (left i) x - b i * v (right i) x) := by
  let W (i : Fin m) := ((M.witness (left i)).smul (a i)).sub
    ((M.witness (right i)).smul (b i))
  let H (i : Fin m) : DeGiorgi.MemW1pWitness 2
      (fun x => sphereFromPlaneFunction
        (fun y => a i * v (left i) y - b i * v (right i) y) (M.projection (planeSphere x))) univ :=
    (W i).congr_ae (Eventually.of_forall fun x =>
      (sphereFromPlaneFunction_linear_difference _ _ _ _ _).symm)
  exact {
    function := M.function
    normalized := M.normalized
    conformal := M.conformal
    circle := M.circle
    projection := M.projection
    projection_continuous := M.projection_continuous
    projection_inverse := M.projection_inverse
    projection_outside := M.projection_outside
    projection_component := M.projection_component
    witness := H
    gradient_zero := by
      intro i j
      filter_upwards [M.gradient_zero (left i) j, M.gradient_zero (right i) j] with x hl hr hx
      change a i * (M.witness (left i)).weakGrad x j +
        (-1) * (b i * (M.witness (right i)).weakGrad x j) = 0
      rw [hl hx, hr hx]
      ring }

end CompactScalarCircleModel
end CircleDomainRigidity

end

end OAI
