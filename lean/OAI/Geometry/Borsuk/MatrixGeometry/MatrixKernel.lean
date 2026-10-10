import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.SphereMoments
import OAI.Geometry.Borsuk.SphereGeometry.IntegralLift
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixNorm

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixKernel
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "Ek" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma matrix_abs_action_norm_sq (A : Matrix ν ν ℝ) (x : Ek) :
    ‖op (CFC.abs A) x‖ ^ 2 = ‖op A x‖ ^ 2 := by
  rw [matrix_action_norm_sq, (CFC.abs_nonneg A).star_eq, CFC.abs_mul_abs,
    ← matrix_action_norm_sq]

lemma matrix_abs_kernel {A : Matrix ν ν ℝ} {x : Ek} (hx : op A x = 0) :
    op (CFC.abs A) x = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [matrix_abs_action_norm_sq, hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]

lemma matrix_parts_kernel {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {x : Ek} (hx : op A x = 0) : op A⁺ x = 0 ∧ op A⁻ x = 0 := by
  have habs := matrix_abs_kernel hx
  constructor
  · have h := congrArg (fun B : Matrix ν ν ℝ => op B x) (CFC.abs_add_self A hA)
    have hh : (2 : ℝ) • op A⁺ x = 0 := by
      simpa only [map_add, add_apply, two_smul, hx, habs, add_zero] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  · have h := congrArg (fun B : Matrix ν ν ℝ => op B x) (CFC.abs_sub_self A hA)
    have hh : (2 : ℝ) • op A⁻ x = 0 := by
      simpa only [map_sub, sub_apply, two_smul, hx, habs, sub_zero,
        map_add, add_apply] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

lemma matrix_image_orthogonal_kernel {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {x : Ek} (hx : op A x = 0) (y : Ek) : ⟪x, op A y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, hA.star_eq, hx, inner_zero_left]

end MatrixKernel

section PositiveExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def positiveExtension (f : E → ι → ℝ) (Q : Matrix ν ν ℝ) : ι → ℝ :=
  integralLift f (op (CFC.sqrt Q))

omit [Nonempty ν] in
lemma Admissible.positiveExtension_nonneg {f : E → ι → ℝ} (hf : Admissible f)
    (Q : Matrix ν ν ℝ) (i : ι) : 0 ≤ positiveExtension f Q i :=
  hf.integralLift_nonneg _ _

lemma Admissible.positiveExtension_sum {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) : ∑ i, positiveExtension f Q i = Matrix.trace Q := by
  classical
  rw [positiveExtension, hf.integralLift_sum]
  simp_rw [sqrt_action_norm_sq Q hQ, Matrix.inner_toEuclideanCLM]
  rw [sphere_quadratic_integral]
  have hn : (Fintype.card ν : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  field_simp

lemma Admissible.positiveExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (positiveExtension f) {Q : Matrix ν ν ℝ | 0 ≤ Q} := by
  have hc : Continuous (fun Q : Matrix ν ν ℝ => op Q) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hf.integralLift_continuous.comp_continuousOn
    (hc.comp_continuousOn CFC.continuousOn_sqrt)

omit [Nonempty ν] [Fintype ι] in
lemma positiveExtension_smul_nonneg (f : E → ι → ℝ)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    positiveExtension f (t • Q) = t • positiveExtension f Q := by
  unfold positiveExtension
  rw [matrix_sqrt_smul hQ ht, map_smul,
    integralLift_smul_nonneg f _ (Real.sqrt_nonneg t), Real.sq_sqrt ht]

lemma Admissible.positiveExtension_support {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) (i : ι) :
    0 < positiveExtension f Q i ↔ ∃ v : E,
      v ∈ LinearMap.range (op Q).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [positiveExtension, hf.integralLift_support, matrix_sqrt_range Q hQ]

end PositiveExtension

end BorsukNine

end OAI
