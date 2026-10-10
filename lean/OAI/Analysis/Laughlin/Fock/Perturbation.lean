import Mathlib.Analysis.InnerProductSpace.Basic
import OAI.Analysis.Laughlin.Asymptotics.Perturbation
import OAI.Analysis.Laughlin.Asymptotics.TruncatedScaling
import OAI.Analysis.Laughlin.Fock.Inner

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem occupation_coefficient_perturbation {I : Type*} [Fintype I] (Q : ℕ)
    (R : Finset (Fin (Q+1)) → I → I → ℝ) (v : I → Space Q)
    (ε : ℝ) (hε : 0 ≤ ε) (hR : ∀ A i j, |R A i j| ≤ ε) :
    |∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j, R A i j *
      ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, occupationNormSq Q (v i) := by
  calc
    _ ≤ ∑ A : Finset (Fin (Q+1)), |∑ i, ∑ j, R A i j *
        ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : Finset (Fin (Q+1)), ε * (Fintype.card I : ℝ) *
        ∑ i, ‖(occupationBasis Q).repr (v i) A‖^2 :=
      Finset.sum_le_sum (fun A hA => quadratic_perturbation_bound (R A)
        (fun i => (occupationBasis Q).repr (v i) A) ε hε (hR A))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rfl

theorem truncatedInverse_inner (L Q : ℕ) (x y : Space Q) :
    occupationInner Q (truncatedScalingInv L Q x) (truncatedScalingInv L Q y) =
      ∑ A : Finset (Fin (Q+1)), (((truncatedDiagonals L Q A)⁻¹)^2 : ℝ) *
        (star ((occupationBasis Q).repr x A) * (occupationBasis Q).repr y A) := by
  simp only [occupationInner,truncatedScalingInv_coordinate,star_mul,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl; intro A hA
  push_cast
  ring

end Laughlin.Fock

end OAI
