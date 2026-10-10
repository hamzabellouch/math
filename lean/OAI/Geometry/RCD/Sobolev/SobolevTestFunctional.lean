import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Energy and L² source terms as compact-test functionals -/

open MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def sobolevSourceFunctional (q : SobolevSpace μ hQ) (ρ : Lp ℝ 2 μ) :
    SobolevSpace μ hQ →ₗ[ℝ] ℝ where
  toFun ψ := energyForm μ hQ q ψ + inner ℝ ρ (SobolevSpace.toLp μ hQ ψ)
  map_add' ψ η := by
    rw [energyForm_add_right, map_add, inner_add_right]
    ring
  map_smul' c ψ := by
    rw [energyForm_smul_right, map_smul, real_inner_smul_right]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

end RegularPointCoordinates

end

end OAI
