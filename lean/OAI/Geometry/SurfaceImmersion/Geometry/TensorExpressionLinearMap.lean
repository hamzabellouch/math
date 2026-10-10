import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTensorPullback

namespace OAI

/-! Fixed smooth changes of tensor trivialization act on finite jet
polynomials by finite linear combinations with positional coefficients. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial

def tensorLinearCoefficient (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (k l : Fin 3) : LowJet × ℝ → ℝ :=
  fun z => L (lowPosition z.1) (Pi.single l 1) k

lemma tensorLinearCoefficient_smooth
    {L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor}
    (hL : ContDiff ℝ ∞ L) (k l : Fin 3) :
    ContDiff ℝ ∞ (tensorLinearCoefficient L k l) := by
  have hs : ContDiff ℝ ∞ (fun x => L x (Pi.single l 1) k) :=
    contDiff_pi.mp (hL.clm_apply contDiff_const) k
  exact hs.comp (lowPosition.contDiff.comp contDiff_fst)

namespace TensorExpression

def mapLinear (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (E : TensorExpression) : TensorExpression := fun k =>
  Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorLinearCoefficient L k l)).mul (E l))

lemma mapLinear_smooth {L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor}
    (hL : ContDiff ℝ ∞ L) {E : TensorExpression}
    (hE : ∀ k, (E k).SmoothCoeffs univ) (k : Fin 3) :
    (mapLinear L E k).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro l _
  exact Expression.smoothCoeffs_mul (tensorLinearCoefficient_smooth hL k l).contDiffOn (hE l)

lemma mapLinear_eval (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (E : TensorExpression) (G : Base → Space) (x : Base) (t : ℝ) :
    eval (mapLinear L E) G (x,t) = L x (eval E G (x,t)) := by
  have hb : (∑ l : Fin 3, (eval E G (x,t)) l • Pi.single l (1 : ℝ)) = eval E G (x,t) := by
    ext k
    simp [Pi.single_apply]
  rw [← hb,map_sum]
  funext k
  change (Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorLinearCoefficient L k l)).mul (E l))).eval G (x,t) = _
  rw [Expression.sumFinset,Expression.eval_sumList,
    ← List.sum_toFinset _ Finset.univ.nodup_toList,Finset.toList_toFinset]
  simp only [Expression.eval_mul,Expression.eval,tensorLinearCoefficient,lowPosition_lowJet,
    map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

end TensorExpression

namespace Perturbation

def mapTensorPolynomial {n : ℕ} (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (P : Fin 3 → Fin n → Expression) : Fin 3 → Fin n → Expression :=
  fun k r => TensorExpression.mapLinear L (fun l => P l r) k

lemma mapTensorPolynomial_smooth {n : ℕ}
    {L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor} (hL : ContDiff ℝ ∞ L)
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    (k : Fin 3) (r : Fin n) : (mapTensorPolynomial L P k r).SmoothCoeffs univ :=
  TensorExpression.mapLinear_smooth hL (fun l => hP l r) k

lemma mapTensorPolynomial_eval {n : ℕ}
    (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor) (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) (G : Base → Space) (t : ℝ) (x : Base) :
    coordinatePolynomialValue (mapTensorPolynomial L P) ε G t (planeCoordinateIsometry x) =
      L x (coordinatePolynomialValue P ε G t (planeCoordinateIsometry x)) := by
  rw [coordinatePolynomialValue_eq_tensor_sum,coordinatePolynomialValue_eq_tensor_sum,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  congr 1
  exact TensorExpression.mapLinear_eval L (fun l => P l r) G x t

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
