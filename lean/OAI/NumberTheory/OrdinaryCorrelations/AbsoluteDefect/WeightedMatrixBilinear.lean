import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Localization
open Matrix Finset
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weighted_matrix_bilinear (M : Matrix ι ι ℂ) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (F G : ι → ℂ) (hF : ∀ i,‖F i‖≤1) (hG : ∀ i,‖G i‖≤1) :
    ‖∑ i,∑ j,F i*M i j*G j*(Real.sqrt (w i):ℂ)*(Real.sqrt (w j):ℂ)‖ ≤
      ‖M‖*∑ i,w i := by
  let u : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => star (F i)*(Real.sqrt (w i):ℂ))
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => G i*(Real.sqrt (w i):ℂ))
  have hvec (f : ι → ℂ) (hf : ∀ i,‖f i‖≤1) :
      ‖(WithLp.toLp 2 (fun i => f i*(Real.sqrt (w i):ℂ)) : EuclideanSpace ℂ ι)‖ ≤
        Real.sqrt (∑ i,w i) := by
    apply Real.le_sqrt_of_sq_le
    rw [EuclideanSpace.norm_sq_eq]
    apply sum_le_sum
    intro i hi
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (hw i)]
    exact mul_le_of_le_one_left (hw i) (by nlinarith [norm_nonneg (f i),hf i])
  have hu : ‖u‖≤Real.sqrt (∑ i,w i) := hvec (fun i => star (F i)) (by simpa)
  have hv : ‖v‖≤Real.sqrt (∑ i,w i) := hvec G hG
  have heq : (∑ i,∑ j,F i*M i j*G j*(Real.sqrt (w i):ℂ)*(Real.sqrt (w j):ℂ))=
      inner ℂ u ((WithLp.toLp 2 (M *ᵥ v.ofLp) : EuclideanSpace ℂ ι)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [v,u,
      dotProduct,Matrix.mulVec,Pi.star_apply,star_mul,Complex.star_def,
      Complex.conj_ofReal,Complex.conj_conj,Finset.sum_mul]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  rw [heq]
  calc
    ‖inner ℂ u ((WithLp.toLp 2 (M *ᵥ v.ofLp) : EuclideanSpace ℂ ι))‖ ≤ ‖u‖*‖(WithLp.toLp 2 (M *ᵥ v.ofLp) : EuclideanSpace ℂ ι)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖*(‖M‖*‖v‖) := mul_le_mul_of_nonneg_left (by
      exact Matrix.l2_opNorm_mulVec M v) (norm_nonneg _)
    _ ≤ Real.sqrt (∑ i,w i)*(‖M‖*Real.sqrt (∑ i,w i)) := by
      exact mul_le_mul hu (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = ‖M‖*∑ i,w i := by
      rw [mul_left_comm,Real.mul_self_sqrt (sum_nonneg (fun i hi => hw i))]

end
end OrdinaryCorrelations.Localization

end

end OAI
