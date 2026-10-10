import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import OAI.Geometry.NodalSets.Elliptic.RealWeightedTransport

namespace OAI

namespace Yau
open scoped ContDiff
noncomputable section
variable {n : ℕ}

lemma real_coordPartial_add (u v : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ u y+v y) x i = coordPartial u x i+coordPartial v x i := by
  unfold coordPartial
  rw [fderiv_fun_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  rfl

lemma real_coordPartial_const_mul (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (a : ℝ) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ a*u y) x i = a*coordPartial u x i := by
  rw [real_coordPartial_mul _ _ contDiff_const hu]
  simp [coordPartial]

lemma real_coordPartial_commute (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (x : Coord n) (i j : Fin n) :
    coordPartial (fun y ↦ coordPartial u y j) x i =
      coordPartial (fun y ↦ coordPartial u y i) x j := by
  have hd := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.comp_zero,
    ContinuousLinearMap.flip_apply,zero_add]
  exact hu.contDiffAt.isSymmSndFDerivAt (by simp) _ _

lemma real_coordPartial_pairing (u : Coord n → ℝ) (V : Coord n → Coord n)
    (hu : ContDiff ℝ ∞ u) (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k))
    (x : Coord n) (i : Fin n) :
    coordPartial (pairing u V) x i =
      ∑ k, (coordPartial (fun y ↦ coordPartial u y k) x i*V x k +
        coordPartial u x k*coordPartial (fun y ↦ V y k) x i) := by
  unfold pairing
  rw [real_coordPartial_sum _ (fun k ↦ (real_coordPartial_smooth u hu k).mul (hV k))]
  simp only [real_coordPartial_mul _ _ (real_coordPartial_smooth u hu _) (hV _)]

end
end Yau

end OAI
