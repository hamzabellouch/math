import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockDerivativeSum
import OAI.Probability.SKBarriers.Interpolation.FiniteCovarianceComparison

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {S : Type}

def blockObservable {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) : Fin (blockDimension D N k) → S → ℝ :=
  Fin.addCases H (fun t => F (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)

def blockInterpolationChoice (D N k : ℕ) : Fin (blockDimension D N k) → Bool :=
  Fin.addCases (fun _ => true) (fun _ => false)

theorem blockObservable_disorder {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (i : Fin D) :
    blockObservable H F (Fin.castAdd ((k+1)*N) i)=H i := by
  simp only [blockObservable,Fin.addCases_left]

theorem blockObservable_field {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (b : Fin (k+1)) (i : Fin N) :
    blockObservable H F (fieldIndex D N k b i)=F b i := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockObservable,Fin.addCases_right,Equiv.symm_apply_apply]

theorem blockObservable_covariance {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (s t : S) :
    (∑ i, interpolationRate (blockDimension D N k) (blockInterpolationChoice D N k) i*
      (blockObservable H F i s*blockObservable H F i t))=
      (1/2:ℝ)*(∑ i, H i s*H i t)-(1/2:ℝ)*(∑ b, ∑ i, F b i s*F b i t) := by
  rw [Fin.sum_univ_add]
  simp only [interpolationRate,blockInterpolationChoice,blockObservable,Fin.addCases_left,
    Fin.addCases_right,Bool.false_eq_true,ite_true,ite_false]
  rw [← finProdFinEquiv.sum_comp (fun u : Fin ((k+1)*N) =>
    -(1/2:ℝ)*(F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 s*
      F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 t))]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,← Finset.mul_sum]
  ring

theorem blockObservable_partial_covariance {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (b : Fin (k+1)) (s t : S) :
    partialObservableCovariance (blockDimension D N k) (blockObservable H F)
      (interpolationRate (blockDimension D N k) (blockInterpolationChoice D N k))
      (blockLevel D N k b) s t=
      (1/2:ℝ)*(∑ i, H i s*H i t)-
        (1/2:ℝ)*(∑ a, if a≤b then ∑ i, F a i s*F a i t else 0) := by
  unfold partialObservableCovariance
  rw [Fin.sum_univ_add]
  have hd (i : Fin D) : (Fin.castAdd ((k+1)*N) i).val < (blockLevel D N k b).val := by
    simp only [Fin.val_castAdd,blockLevel_val]
    omega
  simp only [hd,ite_true,interpolationRate,blockInterpolationChoice,blockObservable,
    Fin.addCases_left,Fin.addCases_right,Bool.false_eq_true,ite_false]
  rw [← finProdFinEquiv.sum_comp (fun u : Fin ((k+1)*N) =>
    if (Fin.natAdd D u).val < (blockLevel D N k b).val then
      -(1/2:ℝ)*(F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 s*
        F (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2 t) else 0)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,← fieldIndex_eq_natAdd,
    fieldIndex_lt_blockLevel_iff,← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_ite_irrel,Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [neg_mul,mul_zero,Finset.sum_const_zero,Finset.sum_neg_distrib,← Finset.mul_sum,neg_zero]

end SK.Analytic

end
end

end OAI
