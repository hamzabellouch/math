import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkModel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators ContDiff
namespace SphericalPerceptronFreeEnergy

def ambientTensorFeature (N p : ℕ) (x : Spin N) : EuclideanSpace ℝ (SpinTensorIndex N p) :=
  WithLp.toLp 2 (fun i => ∏ j, x (i j))

lemma ambientTensorFeature_contDiff (N p : ℕ) : ContDiff ℝ ∞ (ambientTensorFeature N p) := by
  apply (PiLp.contDiff_toLp).comp
  apply contDiff_pi.mpr
  intro i
  exact contDiff_prod (fun j _ => (EuclideanSpace.proj (i j) : Spin N →L[ℝ] ℝ).contDiff)

lemma ambientTensorFeature_inner (N p : ℕ) (x y : Spin N) :
    inner ℝ (ambientTensorFeature N p x) (ambientTensorFeature N p y) = inner ℝ x y ^ p := by
  change (∑ i : SpinTensorIndex N p, (∏ j, y (i j))*(∏ j, x (i j))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (i : Fin N) => y i*x i)]
  change (∏ _ : Fin p, inner ℝ x y)=inner ℝ x y^p
  simp

def ambientBulkFeature (N : ℕ) (v : ℕ→ℝ) (x : Spin N) : BulkMark N :=
  WithLp.toLp 2 fun i => match i with
    | .inl _ => 0
    | .inr ⟨j,t⟩ => bulkAmplitude N v j*ambientTensorFeature N (bulkDegree j) x t

lemma ambientBulkFeature_eq (N : ℕ) (v : ℕ→ℝ) (x : NormalizedSpin N) :
    ambientBulkFeature N v x.val=bulkFeature N v x := by
  ext i
  cases i <;> simp [ambientBulkFeature,bulkFeature,enrichedFeature,ambientTensorFeature,spinTensorFeature]

lemma ambientBulkFeature_contDiff (N : ℕ) (v : ℕ→ℝ) : ContDiff ℝ ∞ (ambientBulkFeature N v) := by
  apply (PiLp.contDiff_toLp).comp
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiff_const
  | inr i => exact contDiff_const.mul ((EuclideanSpace.proj i.2).contDiff.comp (ambientTensorFeature_contDiff _ _))

lemma ambientBulkFeature_inner (N : ℕ) (v : ℕ→ℝ) (x y : Spin N) :
    inner ℝ (ambientBulkFeature N v x) (ambientBulkFeature N v y)=
      ∑ j : Fin N, bulkAmplitude N v j^2*inner ℝ x y^(j.val+1) := by
  change (∑ i : EnrichedIndex N N bulkDegree,
    ambientBulkFeature N v y i*ambientBulkFeature N v x i)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [ambientBulkFeature,mul_zero,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ambientTensorFeature_inner N (j.val+1) x y]
  change (∑ i, bulkAmplitude N v j*ambientTensorFeature N _ y i*
    (bulkAmplitude N v j*ambientTensorFeature N _ x i)) =
    bulkAmplitude N v j^2*(∑ i, ambientTensorFeature N _ y i*ambientTensorFeature N _ x i)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by dsimp [bulkDegree]; ring

def bulkCovarianceDerivative (N : ℕ) (v : ℕ→ℝ) (r : ℝ) : ℝ :=
  ∑ j : Fin N, bulkAmplitude N v j^2*(j.val+1)*r^j.val

lemma ambientBulkFeature_deriv_inner (N : ℕ) (v : ℕ→ℝ) (x y z : Spin N) :
    inner ℝ (fderiv ℝ (ambientBulkFeature N v) x z) (ambientBulkFeature N v y)=
      bulkCovarianceDerivative N v (inner ℝ x y)*inner ℝ z y := by
  have hd := ((innerSL ℝ (ambientBulkFeature N v y)).hasFDerivAt.comp x
    ((ambientBulkFeature_contDiff N v).differentiable (by norm_num) x).hasFDerivAt).fderiv
  have he : (fun x => inner ℝ (ambientBulkFeature N v y) (ambientBulkFeature N v x))=
      (fun x => ∑ j : Fin N, bulkAmplitude N v j^2*inner ℝ y x^(j.val+1)) := by
    funext x; exact ambientBulkFeature_inner N v y x
  have hh : HasFDerivAt (fun x : Spin N => ∑ j : Fin N, bulkAmplitude N v j^2*inner ℝ y x^(j.val+1))
      (∑ j : Fin N, (bulkAmplitude N v j^2*((j.val+1:ℕ):ℝ)*inner ℝ y x^j.val) • innerSL ℝ y) x := by
    have ht (j : Fin N) : HasFDerivAt (fun x : Spin N => bulkAmplitude N v j^2*inner ℝ y x^(j.val+1))
        ((bulkAmplitude N v j^2*((j.val+1:ℕ):ℝ)*inner ℝ y x^j.val) • innerSL ℝ y) x := by
      simpa only [Nat.add_sub_cancel,nsmul_eq_mul,smul_smul,smul_eq_mul,coe_innerSL_apply,mul_assoc] using
        (((innerSL ℝ y).hasFDerivAt (x:=x)).pow (j.val+1)).const_mul (bulkAmplitude N v j^2)
    exact HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => ht j)
  simp only [Function.comp_def,coe_innerSL_apply] at hd
  rw [he,hh.fderiv] at hd
  have hx := congrArg (fun L : Spin N→L[ℝ]ℝ => L z) hd
  simpa only [sum_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,coe_innerSL_apply,bulkCovarianceDerivative,Finset.sum_mul,
    real_inner_comm y x,real_inner_comm y z,real_inner_comm (ambientBulkFeature N v y),Nat.cast_add,Nat.cast_one] using hx.symm

end SphericalPerceptronFreeEnergy
end

end OAI
