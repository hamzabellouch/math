import Mathlib
import OAI.Analysis.FreeWords.WeakCompact

namespace OAI

noncomputable section

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

namespace UniversalStrongKK

section OperatorMean

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (m : ScalarMean G)

variable [CompleteSpace H]

end OperatorMean

end UniversalStrongKK

open scoped Topology

namespace UniversalStrongKK

section UltraMean

variable {I : Type*} [TopologicalSpace I]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UltraMean

end UniversalStrongKK

namespace UniversalStrongKK

open scoped InnerProductSpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UniversalStrongKK

namespace UniversalStrongKK

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

section OperatorMeanAlgebra

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (m : ScalarMean G)

theorem operatorMean_add (S T : G →ᵇ (H →L[ℂ] H)) :
    operatorMean m (S + T) = operatorMean m S + operatorMean m T := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [add_apply, inner_add_left, inner_operatorMean]
  rw [show operatorCoefficient (S + T) x y =
      operatorCoefficient S x y + operatorCoefficient T x y by ext; simp]
  exact map_add m.map _ _

theorem operatorMean_smul (c : ℂ) (T : G →ᵇ (H →L[ℂ] H)) :
    operatorMean m (c • T) = c • operatorMean m T := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [smul_apply, inner_smul_left, inner_operatorMean]
  rw [show operatorCoefficient (c • T) x y = star c • operatorCoefficient T x y by
    ext; simp [mul_comm]]
  exact map_smul m.map (star c) _

noncomputable def operatorMeanCLM : (G →ᵇ (H →L[ℂ] H)) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := operatorMean m
      map_add' := operatorMean_add m
      map_smul' := operatorMean_smul m }
    1 (fun T => by simpa using norm_operatorMean_le m T)

@[simp] theorem operatorMeanCLM_apply (T : G →ᵇ (H →L[ℂ] H)) :
    operatorMeanCLM m T = operatorMean m T := rfl

theorem ScalarMean.map_const (c : ℂ) : m.map (BoundedContinuousFunction.const G c) = c := by
  rw [show BoundedContinuousFunction.const G c = c • (1 : G →ᵇ ℂ) by ext; simp]
  simp [m.map_one]

@[simp] theorem operatorMean_const (T : H →L[ℂ] H) :
    operatorMean m (BoundedContinuousFunction.const G T) = T := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [inner_operatorMean]
  rw [show operatorCoefficient (BoundedContinuousFunction.const G T) x y =
      BoundedContinuousFunction.const G ⟪T x, y⟫_ℂ by ext; rfl]
  exact m.map_const _

theorem operatorMean_bimodule (B C : H →L[ℂ] H) (T : G →ᵇ (H →L[ℂ] H)) :
    operatorMean m (BoundedContinuousFunction.const G B * T *
      BoundedContinuousFunction.const G C) = B * operatorMean m T * C := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [inner_operatorMean]
  change _ = ⟪B (operatorMean m T (C x)), y⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_right, inner_operatorMean]
  congr 1
  ext g
  simp only [operatorCoefficient_apply, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.const_apply, mul_apply_eq_comp]
  exact (ContinuousLinearMap.adjoint_inner_right B _ _).symm

theorem operatorMean_star (T : G →ᵇ (H →L[ℂ] H)) :
    operatorMean m (star T) = star (operatorMean m T) := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [inner_operatorMean]
  rw [show operatorCoefficient (star T) x y = star (operatorCoefficient T y x) by
    ext g
    simp only [operatorCoefficient_apply, BoundedContinuousFunction.star_apply]
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      ← starRingEnd_apply, inner_conj_symm]]
  rw [m.map_star, ← inner_operatorMean, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, ← starRingEnd_apply, inner_conj_symm]

end OperatorMeanAlgebra

end UniversalStrongKK
end

end OAI
