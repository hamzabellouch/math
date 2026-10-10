import Mathlib
import OAI.Analysis.AffineBernstein.FlatLogEuler
import OAI.Analysis.AffineBernstein.NewtonBasisFurther
import OAI.Analysis.AffineBernstein.RoundContractions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma supportNewtonPair_eq_inverse (b c : OrthonormalBasis (ι ⊕ Unit) ℝ E)
    {H : E → ℝ} {e : E} (hH : ContDiffAt ℝ ∞ H e) (hc : c (Sum.inr ()) = e)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) e v e = 0)
    (hR : (Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) e
      (c (Sum.inl i)) (c (Sum.inl j))).det ≠ 0) (f g : E → ℝ) :
    let R := Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) e
      (c (Sum.inl i)) (c (Sum.inl j))
    supportNewtonTensor b H e (tangentProjection e (gradient f e))
      (tangentProjection e (gradient g e)) =
      R.det * flatInversePair R (fun i => c (Sum.inl i)) f g e := by
  subst e
  dsimp only
  rw [roundTensorPair_adapted c]
  have hcof (i j : ι) : supportNewtonTensor b H (c (Sum.inr ()))
      (c (Sum.inl j)) (c (Sum.inl i)) =
      (Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) (c (Sum.inr ()))
        (c (Sum.inl i)) (c (Sum.inl j))).det *
      (Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) (c (Sum.inr ()))
        (c (Sum.inl i)) (c (Sum.inl j)))⁻¹ i j := by
    rw [supportNewtonTensor_isSymm b hH,
      supportNewtonTensor_eq_tangential_cofactor b c hH rfl hr,matrix_adjugate_entry hR]
  simp only [hcof,flatInversePair,dirDeriv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma supportNewtonTrace_eq_inverse (b c : OrthonormalBasis (ι ⊕ Unit) ℝ E)
    {H g : E → ℝ} {e : E} (hH : ContDiffAt ℝ ∞ H e) (hc : c (Sum.inr ()) = e)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) e v e = 0)
    (hR : (Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) e
      (c (Sum.inl i)) (c (Sum.inl j))).det ≠ 0)
    (hg : ContDiffAt ℝ ∞ g e) (hgr : fderiv ℝ g e e = 0) :
    let R := Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) e
      (c (Sum.inl i)) (c (Sum.inl j))
    roundHessianContraction b (supportNewtonTensor b H) g e =
      R.det * flatInverseTrace R (fun i => c (Sum.inl i)) g e := by
  subst e
  dsimp only
  rw [roundHessianContraction_basis b c,roundHessianContraction_adapted c _ hg]
  have hcof (i j : ι) : supportNewtonTensor b H (c (Sum.inr ()))
      (c (Sum.inl j)) (c (Sum.inl i)) =
      (Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) (c (Sum.inr ()))
        (c (Sum.inl i)) (c (Sum.inl j))).det *
      (Matrix.of fun i j : ι => fderiv ℝ (fderiv ℝ H) (c (Sum.inr ()))
        (c (Sum.inl i)) (c (Sum.inl j)))⁻¹ i j := by
    rw [supportNewtonTensor_isSymm b hH,
      supportNewtonTensor_eq_tangential_cofactor b c hH rfl hr,matrix_adjugate_entry hR]
  simp only [hcof,hgr,zero_mul,sub_zero,flatInverseTrace,dirDeriv_eq_second hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end AffineBernstein
end

end OAI
