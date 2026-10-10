import OAI.Geometry.SurfaceImmersion.Correction.CoordinatePolynomialPullback
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialScalar

namespace OAI

/-! Pullback of finite tensor expressions under fixed coordinate changes.
The Jacobian factors, coefficient substitution, and higher jet atoms are
all constructed, so the evaluation identity assumes no tensor covariance. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Matrix Topology

namespace ClosedSurfaceR4.JetPolynomial

abbrev TensorExpression := Fin 3 → Expression

/-- The derivative of the coordinate map in the real pair coordinates
used by the three-component tensor representation. -/
def tensorCoordinateDerivative (T : Base → Base) (x : Base) :
    SmallModes.Base →L[ℝ] SmallModes.Base :=
  planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((fderiv ℝ T x).comp
      planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Covariant pullback of a symmetric tensor by the actual derivative. -/
def tensorCoordinatePullbackValue (T : Base → Base) (x : Base) :
    PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
  PhaseMean.pullback (tensorCoordinateDerivative T x)

/-- The three Jacobian coefficients of one pulled-back tensor component. -/
def tensorCoordinateJacobian (T : Base → Base) (k l : Fin 3) (x : Base) : ℝ :=
  let u := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.firstDirection k))
  let v := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.secondDirection k))
  ![u 0 * v 0,u 0 * v 1 + u 1 * v 0,u 1 * v 1] l

lemma tensorCoordinateJacobian_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorCoordinateJacobian T k l) := by
  have hd (v : Base) (a : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ T x v a) :=
    contDiff_pi.mp ((hT.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) a
  fin_cases l
  · exact (hd _ 0).mul (hd _ 0)
  · exact ((hd _ 0).mul (hd _ 1)).add ((hd _ 1).mul (hd _ 0))
  · exact (hd _ 1).mul (hd _ 1)

lemma tensorCoordinateJacobian_sum (T : Base → Base) (x : Base)
    (A : PhaseMean.Tensor) (k : Fin 3) :
    (∑ l : Fin 3, tensorCoordinateJacobian T k l x * A l) =
      tensorCoordinatePullbackValue T x A k := by
  rw [Fin.sum_univ_three]
  let u := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.firstDirection k))
  let v := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.secondDirection k))
  change u 0 * v 0 * A 0 + (u 0 * v 1 + u 1 * v 0) * A 1 + u 1 * v 1 * A 2 =
    A 0 * u 0 * v 0 + A 1 * (u 0 * v 1 + u 1 * v 0) + A 2 * u 1 * v 1
  ring

/-- Store a Jacobian factor as an actual smooth positional coefficient. -/
def tensorJacobianCoefficient (T : Base → Base) (k l : Fin 3) : LowJet × ℝ → ℝ :=
  fun z => tensorCoordinateJacobian T k l (lowPosition z.1)

lemma tensorJacobianCoefficient_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorJacobianCoefficient T k l) :=
  (tensorCoordinateJacobian_smooth hT k l).comp (lowPosition.contDiff.comp contDiff_fst)

namespace TensorExpression

/-- Evaluation in the original coordinate chart. -/
def eval (E : TensorExpression) (G : Base → Space) (z : Base × ℝ) : PhaseMean.Tensor :=
  fun k => (E k).eval G z

/-- Pull back both the scalar jet expressions and their tensor basis. -/
def coordinatePullback (E : TensorExpression) (T S : Base → Base) : TensorExpression :=
  fun k => Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorJacobianCoefficient T k l)).mul ((E l).localCoordinatePullback T S))

lemma coordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {E : TensorExpression} (hE : ∀ k, (E k).SmoothCoeffs univ) (k : Fin 3) :
    (coordinatePullback E T S k).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro l _
  exact Expression.smoothCoeffs_mul (tensorJacobianCoefficient_smooth hT k l).contDiffOn
    (Expression.localCoordinatePullback_smooth hT hS (hE l))

/-- An exact tensor evaluation identity from genuine local inverse germs
and the actual map relation. -/
theorem coordinatePullback_eval {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (E : TensorExpression) (t : ℝ) {x : Base} (hx : x ∈ U) :
    eval (coordinatePullback E T S) H (x,t) =
      tensorCoordinatePullbackValue T x (eval E G (T x,t)) := by
  funext k
  change (Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorJacobianCoefficient T k l)).mul ((E l).localCoordinatePullback T S))).eval
      H (x,t) = _
  rw [Expression.sumFinset,Expression.eval_sumList,
    ← List.sum_toFinset _ Finset.univ.nodup_toList,Finset.toList_toFinset]
  simp only [Expression.eval_mul,Expression.eval,tensorJacobianCoefficient,lowPosition_lowJet]
  simp_rw [Expression.localCoordinatePullback_eval hT hS hU hST hTS hG hH hrel _ t hx]
  exact tensorCoordinateJacobian_sum T x (eval E G (T x,t)) k

end TensorExpression

namespace Perturbation

/-- Apply the tensor coordinate transformation coefficient by coefficient
to a finite polynomial in the perturbation parameter. -/
def tensorPolynomialCoordinatePullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (T S : Base → Base) : Fin 3 → Fin n → Expression :=
  fun k r => TensorExpression.coordinatePullback (fun l => P l r) T S k

lemma tensorPolynomialCoordinatePullback_smooth {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    (k : Fin 3) (r : Fin n) :
    (tensorPolynomialCoordinatePullback P T S k r).SmoothCoeffs univ :=
  TensorExpression.coordinatePullback_smooth hT hS (fun l => hP l r) k

lemma coordinatePolynomialValue_eq_tensor_sum {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) (t : ℝ) (x : Base) :
    coordinatePolynomialValue P ε G t (planeCoordinateIsometry x) =
      ∑ r : Fin n, ε ^ (r.val+1) • TensorExpression.eval (fun k => P k r) G (x,t) := by
  funext k
  simp only [coordinatePolynomialValue,LinearIsometryEquiv.symm_apply_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,TensorExpression.eval]

/-- The three-component finite polynomial transforms covariantly under
smooth coordinate changes. -/
theorem tensorPolynomialCoordinatePullback_eval {n : ℕ}
    (P : Fin 3 → Fin n → Expression) {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (ε t : ℝ) {x : Base} (hx : x ∈ U) :
    coordinatePolynomialValue (tensorPolynomialCoordinatePullback P T S) ε H t
        (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (coordinatePolynomialValue P ε G t (planeCoordinateIsometry (T x))) := by
  rw [coordinatePolynomialValue_eq_tensor_sum,coordinatePolynomialValue_eq_tensor_sum,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  congr 1
  exact TensorExpression.coordinatePullback_eval hT hS hU hST hTS hG hH hrel
    (fun k => P k r) t hx

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
