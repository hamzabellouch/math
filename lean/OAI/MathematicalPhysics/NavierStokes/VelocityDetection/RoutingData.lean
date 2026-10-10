import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Expanding

namespace OAI

noncomputable section
namespace VelocityDetection
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty

structure RoutingData where
  K : ℝ
  D : ℝ
  K_nonneg : 0 ≤ K
  D_ge_one : 1 ≤ D
  Instruction : ℕ → Type
  finite : ∀ n, Fintype (Instruction n)
  source : ∀ n, Instruction n → ℕ
  target : ∀ n, Instruction n → ℕ
  sign : ∀ n, Instruction n → ℝ
  source_injective : ∀ n, Injective (source n)
  target_injective : ∀ n, Injective (target n)
  source_count : ∀ n c, (source n c : ℝ) ≤ Expanding.count K D n
  target_count : ∀ n c, (target n c : ℝ) ≤ Expanding.count K D (n + 1)
  abs_sign : ∀ n c, |sign n c| = 1

instance (A : RoutingData) (n : ℕ) : Fintype (A.Instruction n) := A.finite n

end VelocityDetection
end

end OAI
