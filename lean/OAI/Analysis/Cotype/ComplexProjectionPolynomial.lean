import OAI.Analysis.Cotype.ComplexDualLift
import OAI.Analysis.Cotype.ProjectionCoefficientDerivative
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

noncomputable section
namespace Cotype

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def complexProjectionProduct : {m : ℕ} → (Fin m → Z →L[ℂ] Z) → Z →L[ℂ] Z
  | 0, _ => 1
  | _+1, P => P 0 * complexProjectionProduct (fun i => P i.succ)

theorem complexProjectionProduct_differentiable {m : ℕ}
    (P : Fin m → ℂ → Z →L[ℂ] Z) (hP : ∀ i, Differentiable ℂ (P i)) :
    Differentiable ℂ (fun z => complexProjectionProduct (fun i => P i z)) := by
  induction m with
  | zero => exact differentiable_const _
  | succ m ih => exact (hP 0).mul (ih (fun i => P i.succ) (fun i => hP i.succ))

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def complexProjectionPolynomial {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (z : ℂ) : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  complexProjectionProduct (fun i => complexDualLift (P i) + z • (1-complexDualLift (P i)))

theorem complexProjectionProduct_lift {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    complexProjectionProduct (fun i => complexDualLift (P i)) =
      complexDualLift (projectionProduct P) := by
  induction m with
  | zero => simp [complexProjectionProduct, projectionProduct]
  | succ m ih => simp [complexProjectionProduct, projectionProduct, ih]

theorem complexProjectionPolynomial_real {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (r : ℝ) :
    complexProjectionPolynomial P (r : ℂ) = complexDualLift (projectionSemigroup P r) := by
  unfold complexProjectionPolynomial projectionSemigroup
  rw [← complexProjectionProduct_lift]
  congr 1
  funext i
  simp only [complexDualLift_add, complexDualLift_smul, complexDualLift_sub, complexDualLift_one]
  congr 1

theorem complexProjectionPolynomial_differentiable {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    Differentiable ℂ (complexProjectionPolynomial P) := by
  apply complexProjectionProduct_differentiable
  intro i
  exact (differentiable_const _).add (differentiable_id.smul_const _)

def complexDualLiftCLM : (Y →L[ℝ] Y) →L[ℝ] (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :=
  ({ toFun := complexDualLift
     map_add' := complexDualLift_add
     map_smul' := complexDualLift_smul } :
    (Y →L[ℝ] Y) →ₗ[ℝ] (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)).mkContinuous 1
      (fun (T : Y →L[ℝ] Y) => by
        change ‖complexDualLift T‖ ≤ (1 : ℝ)*‖T‖
        simp only [complexDualLift_norm, one_mul, le_refl])

@[simp] theorem complexDualLiftCLM_apply (T : Y →L[ℝ] Y) :
    complexDualLiftCLM T = complexDualLift T := rfl

theorem complexProjectionPolynomial_deriv_zero {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j)) :
    deriv (complexProjectionPolynomial P) 0 = complexDualLift (projectionLinearCoefficient P) := by
  have hreal : HasDerivAt (fun r : ℝ => complexProjectionPolynomial P (r : ℂ))
      (complexDualLift (projectionLinearCoefficient P)) 0 := by
    have h := (complexDualLiftCLM (Y := Y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (projectionSemigroup_hasDerivAt_zero P hc)
    convert! h using 1
    funext r
    exact complexProjectionPolynomial_real P r
  have hd := (complexProjectionPolynomial_differentiable P).differentiableAt.hasDerivAt
    (x := (0 : ℂ))
  have hrestrict : HasDerivAt (fun r : ℝ => complexProjectionPolynomial P (r : ℂ))
      (deriv (complexProjectionPolynomial P) 0) 0 := by
    have hcomp := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
      (f := fun r : ℝ => (r : ℂ)) (0 : ℝ) Complex.ofRealCLM.hasDerivAt
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_zero, Complex.ofReal_one,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using! hcomp
  exact (hreal.unique hrestrict).symm

theorem projectionLinearCoefficient_bound_of_complex_circle {R M : ℝ} (hR : 0 < R)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (hc : ∀ i j, Commute (P i) (P j))
    (hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖complexProjectionPolynomial P z‖ ≤ M)
    (y : Y) : ‖projectionLinearCoefficient P y‖ ≤ (M/R)*‖y‖ := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (complexProjectionPolynomial_differentiable P).diffContOnCl hcircle
  rw [complexProjectionPolynomial_deriv_zero P hc, complexDualLift_norm] at h
  exact ContinuousLinearMap.le_of_opNorm_le _ h y

end Cotype

end

end OAI
