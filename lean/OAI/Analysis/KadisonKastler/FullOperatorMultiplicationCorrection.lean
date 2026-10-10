import OAI.Analysis.KadisonKastler.OperatorCochainResidual
import OAI.Analysis.KadisonKastler.MultiplicationCorrectionFromCochains
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

/-! # Constructed multiplication correction on the full operator algebra

The rank-one contraction provides the cochain required by the quantitative
iteration. This proves the full-operator case; no claim about arbitrary
von Neumann subalgebras is made here.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance fullCorrectionOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance fullCorrectionOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

/-- The exact quadratic cochain estimate on all bounded operators. -/
theorem fullOperator_quadraticCochainSolver [Nontrivial H] :
    QuadraticCochainSolver (H →L[ℂ] H) := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨ξ, hξ⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨φ, hφn, hφξ⟩ := exists_dual_vector ℂ ξ (by rw [hξ]; norm_num)
  have hφ : φ ξ = 1 := by simpa [hξ] using hφξ
  intro q hq _ m
  let D := (operatorCochainContraction m.bound hq φ ξ).toLinearMap
  have hD : CompletelyBoundedBy D q := by
    simpa only [hφn, hξ, mul_one] using operatorCochainContraction_complete_bound m.bound hq φ ξ
  have hres : HaagerupBound (m.mul - LinearMap.mul ℂ (H →L[ℂ] H) - linearCoboundary D)
      (2 * q ^ 2) := by
    simpa only [hφn, hξ, mul_one] using
      operatorCochainContraction_residual_bound m.mul m.assoc hq m.bound φ ξ hφ
  have hstar : ∀ x y, star ((m.mul - LinearMap.mul ℂ (H →L[ℂ] H)) x y) =
      (m.mul - LinearMap.mul ℂ (H →L[ℂ] H)) (star y) (star x) := by
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.mul_apply', star_sub, star_mul, m.star_mul]
  exact ⟨cochainSymmetrize D, operator_cochainSymmetrize_bound hD,
    cochainSymmetrize_star D,
    operator_cochainSymmetrize_residual_bound hstar D hres⟩

/-- An associative star product within1/11 of operator multiplication has a
constructed star-preserving correcting equivalence, with complete bound4q. -/
theorem fullOperator_multiplication_correction [Nontrivial H]
    (m : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hms : ∀ x y, star (m x y) = m (star y) (star x))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/11)
    (hb : HaagerupBound (m - LinearMap.mul ℂ (H →L[ℂ] H)) q) :
    ∃ T : (H →L[ℂ] H) ≃ₗ[ℂ] (H →L[ℂ] H),
      (∀ x y, T (m x y) = T x * T y) ∧
      (∀ x, T (star x) = star (T x)) ∧
      CompletelyBoundedBy (T.toLinearMap - LinearMap.id) (4 * q) :=
  multiplication_correction_of_quadratic_cochains fullOperator_quadraticCochainSolver m hm hms hq hq1 hb

end

end KadisonKastler

end OAI
