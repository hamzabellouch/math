import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace RuledApproximation

def comparisonOperator : Plane →L[ℝ] Plane :=
  (2 • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 1 0) +
  ((1 / 8 : ℝ) • EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).smulRight (vec2 0 1)

def SpectralNormComparisonStatement : Prop :=
  (∀ lam : ℝ, Module.End.HasEigenvalue comparisonOperator.toLinearMap lam ↔
    lam = 1 / 2 ∨ lam = -(1 / 2)) ∧
  ‖comparisonOperator‖ = 2 ∧
  (∀ p : Plane, HyperbolicAt 1 comparisonOperator p) ∧
  ¬ ∃ kappa : ℝ, kappa < 1 ∧ ‖comparisonOperator‖ ≤ kappa

def transverseScaling (h : ℝ) (hh : h ≠ 0) : Plane ≃ₗ[ℝ] Plane where
  toFun p := vec2 (p 0) (h * p 1)
  invFun p := vec2 (p 0) (p 1 / h)
  left_inv p := by
    ext i
    fin_cases i <;> simp [vec2, hh]
  right_inv p := by
    ext i
    fin_cases i <;> simp [vec2]
    field_simp
  map_add' p q := by
    ext i
    fin_cases i <;> simp [vec2, mul_add]
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [vec2, mul_left_comm]

def PhysicalScalingInvarianceStatement : Prop :=
  ∀ (h : ℝ) (hh : 0 < h) (A : Plane →ₗ[ℝ] Plane),
    (∀ lam : ℝ, Module.End.HasEigenvalue ((transverseScaling h hh.ne').conj A) lam ↔
      Module.End.HasEigenvalue A lam) ∧
    (((transverseScaling h hh.ne').conj A).comp ((transverseScaling h hh.ne').conj A) = 0 ↔
      A.comp A = 0)

def rescaledComparisonOperator : Plane →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    ((transverseScaling 4 (by norm_num)).conj comparisonOperator.toLinearMap)

def PhysicalNormChangeStatement : Prop :=
  ‖comparisonOperator‖ = 2 ∧ ‖rescaledComparisonOperator‖ = 1 / 2

end RuledApproximation

end

end OAI
