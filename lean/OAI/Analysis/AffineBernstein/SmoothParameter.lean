import Mathlib
import OAI.Analysis.AffineBernstein.NewtonTensor

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SmoothParameter
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/- A twice differentiated eigenvector equation, still valid at a singular
matrix and in dimension one. -/
theorem second_deriv_smul_id {g : ℝ → F} (hg : ContDiff ℝ ∞ g) :
    deriv (deriv (fun t : ℝ => t • g t)) 0 = 2 • deriv g 0 := by
  have hdg (t : ℝ) : HasDerivAt g (deriv g t) t :=
    (hg.differentiable (by simp) t).hasDerivAt
  have he : deriv (fun t : ℝ => t • g t) = fun t => g t + t • deriv g t := by
    funext t
    simpa only [one_smul, id_eq, Pi.smul_def', add_comm] using ((hasDerivAt_id t).smul (hdg t)).deriv
  rw [he]
  have hddg : DifferentiableAt ℝ (deriv g) 0 :=
    ((hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable_deriv_two) 0
  have hh := (hdg 0).add ((hasDerivAt_id (0 : ℝ)).smul hddg.hasDerivAt)
  simpa only [zero_smul, one_smul, add_zero, two_smul, Pi.add_def, Pi.smul_def', id_eq, zero_add] using hh.deriv

end SmoothParameter

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_shift (A : Matrix ι ι ℝ) (i j : ι) :
    ContDiff ℝ ∞ (fun t : ℝ => (A + t • 1).adjugate i j) := by
  apply (contDiff_adjugate_entry i j).comp
  change ContDiff ℝ ∞ (fun t : ℝ => fun l m => (A + t • 1) l m)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

lemma contDiff_det_shift (A : Matrix ι ι ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (A + t • 1).det) := by
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun t : ℝ => fun l m => (A + t • 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

/- A radial null vector of the Hessian is an eigenvector of its Newton
polynomial. No nonsingularity, division by a determinant, or limiting inverse
is used. -/
theorem newtonTensor_radial {A : Matrix ι ι ℝ} {v : ι → ℝ}
    (hv : A *ᵥ v = 0) : ∃ c : ℝ, newtonTensor A *ᵥ v = c • v := by
  let f : ℝ → ℝ := fun t => (A + t • 1).det
  have hf : ContDiff ℝ ∞ f := contDiff_det_shift A
  have hdf : Differentiable ℝ (deriv f) :=
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable_deriv_two
  refine ⟨deriv (deriv f) 0 / 2, ?_⟩
  ext i
  let g : ℝ → ℝ := fun t => ((A + t • 1).adjugate *ᵥ v) i
  have hg : ContDiff ℝ ∞ g := by
    change ContDiff ℝ ∞ (fun t : ℝ => ∑ j, (A + t • 1).adjugate i j * v j)
    exact ContDiff.sum (fun j _ => (contDiff_adjugate_shift A i j).mul contDiff_const)
  have he : (fun t : ℝ => t • g t) = fun t => f t * v i := by
    funext t
    have hB : (A + t • (1 : Matrix ι ι ℝ)) *ᵥ v = t • v := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, zero_add]
    have hb := congrFun (show t • ((A + t • (1 : Matrix ι ι ℝ)).adjugate *ᵥ v) =
        f t • v by
      rw [← Matrix.mulVec_smul, ← hB, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
        Matrix.smul_mulVec, Matrix.one_mulVec]) i
    exact hb
  have hsecond : deriv (deriv (fun t => f t * v i)) 0 = deriv (deriv f) 0 * v i := by
    have hh : deriv (fun t => f t * v i) = fun t => deriv f t * v i := by
      funext t
      exact ((hf.differentiable (by simp) t).hasDerivAt.mul_const (v i)).deriv
    rw [hh]
    exact ((hdf 0).hasDerivAt.mul_const (v i)).deriv
  have he2 := congrArg (fun k : ℝ → ℝ => deriv (deriv k) 0) he
  rw [second_deriv_smul_id hg, hsecond] at he2
  have hg' : deriv g 0 = (newtonTensor A *ᵥ v) i := by
    have hh : HasDerivAt g (∑ j, newtonTensor A i j * v j) 0 := by
      apply HasDerivAt.fun_sum
      intro j _
      rw [newtonTensor_eq_deriv]
      exact ((contDiff_adjugate_shift A i j).differentiable (by simp) 0).hasDerivAt.mul_const (v j)
    exact hh.deriv
  rw [hg'] at he2
  simp only [two_smul, smul_eq_mul, Pi.smul_apply] at he2 ⊢
  linarith

end AffineBernstein
end

end OAI
