import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiTensorAlgebra

namespace OAI

/-! Calabi Norm Algebra. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def tensorVector (T : ConnectionTensor n) : EuclideanSpace ℂ (Fin n × Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => T p.1 p.2.1 p.2.2)

def tensorSquare (T : ConnectionTensor n) : ℝ := (tensorPairAt 1 1 T T).re

lemma tensorPairAt_one_inner (T U : ConnectionTensor n) :
    tensorPairAt 1 1 T U = inner ℂ (tensorVector U) (tensorVector T) := by
  rw [tensorPairAt_one]
  simp only [tensorVector,PiLp.inner_apply,Fintype.sum_prod_type,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    RCLike.inner_apply]
  rfl

lemma tensorSquare_norm (T : ConnectionTensor n) : tensorSquare T = ‖tensorVector T‖^2 := by
  rw [tensorSquare,tensorPairAt_one_inner]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (tensorVector T)).symm

lemma tensorSquare_nonneg (T : ConnectionTensor n) : 0 ≤ tensorSquare T := by
  rw [tensorSquare_norm]
  positivity

lemma tensorSquare_pos {T : ConnectionTensor n} (hT : T ≠ 0) : 0 < tensorSquare T := by
  rw [tensorSquare_norm]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro he
  apply hT
  funext i
  ext a b
  exact congrArg (fun v : EuclideanSpace ℂ (Fin n × Fin n × Fin n) => v (i,a,b)) he

lemma tensorPairAt_cauchy (T U : ConnectionTensor n) :
    ‖tensorPairAt 1 1 T U‖^2 ≤ tensorSquare T*tensorSquare U := by
  rw [tensorPairAt_one_inner,tensorSquare_norm,tensorSquare_norm]
  have hh := norm_inner_le_norm (𝕜 := ℂ) (tensorVector U) (tensorVector T)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hh
  simpa only [mul_pow,mul_comm] using hs

lemma tensorSquare_smul (r : ℝ) (T : ConnectionTensor n) :
    tensorSquare (r • T) = r^2*tensorSquare T := by
  have he : tensorVector (r • T) = r • tensorVector T := rfl
  rw [tensorSquare_norm,he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,tensorSquare_norm]

lemma continuous_tensorSquare : Continuous (tensorSquare (n := n)) := by
  rw [show tensorSquare (n := n) = fun T => ‖tensorVector T‖^2 from funext tensorSquare_norm]
  apply Continuous.pow
  apply Continuous.norm
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun p =>
    (continuous_apply p.2.2).comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))

lemma continuous_tensorVector : Continuous (tensorVector (n := n)) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun p =>
    (continuous_apply p.2.2).comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))

lemma tensorPairAt_one_continuous : Continuous
    (fun q : ConnectionTensor n × ConnectionTensor n => tensorPairAt 1 1 q.1 q.2) := by
  simp_rw [tensorPairAt_one_inner]
  exact Continuous.inner (𝕜 := ℂ) (continuous_tensorVector.comp continuous_snd)
    (continuous_tensorVector.comp continuous_fst)

lemma tensorPairAt_one_smul (r s : ℝ) (T U : ConnectionTensor n) :
    tensorPairAt 1 1 (r • T) (s • U) = ((r*s : ℝ) : ℂ)*tensorPairAt 1 1 T U := by
  simp only [tensorPairAt_one,Pi.smul_apply]
  change (∑ i, (((r:ℂ) • T i)*((s:ℂ) • U i)ᴴ).trace) = _
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.trace_smul,smul_eq_mul,
    ← Complex.ofReal_mul,← Finset.mul_sum]
  rw [mul_comm s r]

end KaehlerCalculus

end
end

end OAI
