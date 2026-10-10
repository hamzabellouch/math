import OAI.MeasureTheory.Falconer.Slicing.GaussianPointBand
import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseMass
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Linear maps and kernel planes for the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianRowMap (A : Fin h → Space d) : Space d →L[ℝ] Space h :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin h => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (A i)))

@[simp] theorem gaussianRowMap_apply (A : Fin h → Space d) (x : Space d) (i : Fin h) :
    gaussianRowMap A x i = inner ℝ x (A i) := by
  change inner ℝ (A i) x = inner ℝ x (A i)
  exact real_inner_comm _ _

theorem gaussianRowMap_eq_coordinates (A : Fin h → Space d) (x : Space d) :
    gaussianRowMap A x = gaussianRowCoordinates A x := by
  ext i
  exact gaussianRowMap_apply A x i

theorem gaussianRowMap_adjoint_basis (A : Fin h → Space d) (i : Fin h) :
    (gaussianRowMap A).adjoint (EuclideanSpace.basisFun (Fin h) ℝ i) = A i := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner,gaussianRowMap_apply]
  exact real_inner_comm _ _

theorem coordinate_norm_le_card_mul (x : Space h) {r : ℝ}
    (hx : ∀ i, |x i| ≤ r) : ‖x‖ ≤ (h:ℝ)*r := by
  calc
    _ = ‖∑ i : Fin h, x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := by
      exact congrArg norm ((EuclideanSpace.basisFun (Fin h) ℝ).sum_repr x).symm
    _ ≤ ∑ i : Fin h, ‖x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := norm_sum_le _ _
    _ = ∑ i : Fin h, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one,mul_one]
    _ ≤ ∑ _ : Fin h, r := Finset.sum_le_sum (fun i _ => hx i)
    _ = _ := by simp

theorem gaussianRowMap_norm_le_of_bands (A : Fin h → Space d) (x : Space d) {r : ℝ}
    (hx : ∀ i, |inner ℝ x (A i)| ≤ r) : ‖gaussianRowMap A x‖ ≤ (h:ℝ)*r :=
  coordinate_norm_le_card_mul _ (by simpa only [gaussianRowMap_apply] using hx)

end Falconer

end OAI
