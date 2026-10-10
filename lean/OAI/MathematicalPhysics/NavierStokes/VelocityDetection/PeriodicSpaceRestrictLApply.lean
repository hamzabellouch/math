import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicHeat

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

@[simp] theorem restrictL_apply {n a b : ℕ} (hab : a ≤ b) (J : compatibleJets n b) :
    restrictL hab J = restrict hab J := rfl

@[simp] theorem restrict_average {n a b : ℕ} (hab : a ≤ b) {k : Coord n → ℝ}
    (hk : Integrable k) (s : ℝ) (J : compatibleJets n b) :
    restrict hab (average k s J) = average k s (restrict hab J) := by
  apply value_injective
  ext X
  simp only [restrict_value, value_average hk]

@[simp] theorem restrict_heat {a b : ℕ} (hab : a ≤ b) (ν t : ℝ)
    (J : compatibleJets 2 b) : restrict hab (heat ν t J) = heat ν t (restrict hab J) := by
  exact restrict_average hab (HeatKernels.integrable_normal 2) _ J

@[simp] theorem restrict_heatGradient {a b : ℕ} (hab : a ≤ b) (ν t : ℝ)
    (i : Fin 2) (J : compatibleJets 2 b) :
    restrict hab (heatGradient ν t i J) = heatGradient ν t i (restrict hab J) := by
  change restrictL hab ((-(Real.sqrt (2 * ν * t))⁻¹) •
    average (HeatKernels.momentKernel i) (-Real.sqrt (2 * ν * t)) J) = _
  rw [map_smul]
  change _ • restrict hab (average _ _ J) = _
  rw [restrict_average hab (HeatKernels.integrable_momentKernel i)]
  rfl

@[simp] theorem restrict_product {n a b : ℕ} (hab : a ≤ b) (J K : compatibleJets n b) :
    restrict hab (product J K) = product (restrict hab J) (restrict hab K) := by
  apply value_injective
  simp only [restrict_value, value_product]

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
