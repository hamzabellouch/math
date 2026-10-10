import Mathlib
import OAI.Analysis.AffineBernstein.BlockNewton
import OAI.Analysis.AffineBernstein.NewtonTensor

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section BlockNewton
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma newtonTensor_fromBlocks_zero (A : Matrix ι ι ℝ) (i j : ι) :
    newtonTensor (Matrix.fromBlocks A 0 0 (0 : Matrix Unit Unit ℝ))
      (Sum.inl i) (Sum.inl j) = A.adjugate i j := by
  rw [newtonTensor_eq_deriv]
  have heq : (fun t : ℝ => (Matrix.fromBlocks A 0 0 (0 : Matrix Unit Unit ℝ) + t • 1).adjugate
      (Sum.inl i) (Sum.inl j)) = fun t : ℝ => t * (A + t • 1).adjugate i j := by
    funext t
    have hb : Matrix.fromBlocks A 0 0 (0 : Matrix Unit Unit ℝ) + t • 1 =
        Matrix.fromBlocks (A + t • 1) 0 0 (t • (1 : Matrix Unit Unit ℝ)) := by
      ext l m
      cases l <;> cases m <;> simp [Matrix.fromBlocks, Matrix.one_apply]
    rw [hb, adjugate_fromBlocks_scalar]
  rw [heq]
  have hd : DifferentiableAt ℝ (fun t : ℝ => (A + t • 1).adjugate i j) 0 := by
    have hh : ContDiff ℝ ∞ (fun t : ℝ => fun l m => (A + t • 1) l m) := by
      apply contDiff_pi.mpr
      intro l
      apply contDiff_pi.mpr
      intro m
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop
    exact ((contDiff_adjugate_entry i j).comp hh).differentiable (by simp) 0
  have hh := ((hasDerivAt_id (0 : ℝ)).mul hd.hasDerivAt).deriv
  simpa only [Pi.mul_def, id_eq, zero_smul, add_zero, zero_mul, mul_one, one_mul] using hh
end BlockNewton

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hasDerivAt_adjugate_add_smul_one (A : Matrix ι ι ℝ) (i j : ι) :
    HasDerivAt (fun t : ℝ => (A + t • 1).adjugate i j) (newtonTensor A i j) 0 := by
  have hh : ContDiff ℝ ∞ (fun t : ℝ => fun l m => (A + t • 1) l m) := by
    apply contDiff_pi.mpr
    intro l
    apply contDiff_pi.mpr
    intro m
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hd := ((contDiff_adjugate_entry i j).comp hh).differentiable (by simp) (0 : ℝ)
  rw [newtonTensor_eq_deriv]
  exact hd.hasDerivAt

lemma newtonTensor_conjugate_orthogonal {Q : Matrix ι ι ℝ}
    (hQ : Q * Qᵀ = 1) (hQt : Qᵀ * Q = 1) (A : Matrix ι ι ℝ) :
    newtonTensor (Qᵀ * A * Q) = Qᵀ * newtonTensor A * Q := by
  ext i j
  rw [newtonTensor_eq_deriv]
  have heq : (fun t : ℝ => (Qᵀ * A * Q + t • 1).adjugate i j) =
      fun t : ℝ => (Qᵀ * (A + t • 1).adjugate * Q) i j := by
    funext t
    have hb : Qᵀ * A * Q + t • 1 = Qᵀ * (A + t • 1) * Q := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hQt]
    rw [hb, adjugate_conjugate_orthogonal hQ hQt]
  rw [heq]
  have hh : HasDerivAt (fun t : ℝ => ∑ k, (∑ l, Qᵀ i l * (A + t • 1).adjugate l k) * Q k j)
      (∑ k, (∑ l, Qᵀ i l * newtonTensor A l k) * Q k j) 0 := by
    apply HasDerivAt.fun_sum
    intro k _
    apply HasDerivAt.mul_const
    apply HasDerivAt.fun_sum
    intro l _
    exact (hasDerivAt_adjugate_add_smul_one A l k).const_mul (Qᵀ i l)
  simpa only [Matrix.mul_apply] using hh.deriv

end AffineBernstein
end

end OAI
