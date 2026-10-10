import OAI.Analysis.Nuclearity.TensorCoefficientFunctional
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Module.RCLike.Extend

namespace OAI

/-! Finite sums of vector functionals, with their norm as functionals on
bounded operators, have bounded operators as their continuous dual. This
finite predual is sufficient for the convex separation step in the
hypertrace argument; no trace-class completion is required here. -/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorCoefficient_norm_le (x y : H) :
    ‖operatorCoefficient x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  intro T
  calc
    ‖operatorCoefficient x y T‖ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm x (T y)
    _ ≤ ‖x‖ * (‖T‖ * ‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg x)
    _ = (‖x‖ * ‖y‖) * ‖T‖ := by ring

abbrev finiteOperatorPredual : Submodule ℂ (StrongDual ℂ (H →L[ℂ] H)) :=
  Submodule.span ℂ (Set.range (fun p : H × H => operatorCoefficient p.1 p.2))

instance finitePredualNormed : NormedAddCommGroup (finiteOperatorPredual (H := H)) :=
  inferInstance

instance finitePredualComplex : NormedSpace ℂ (finiteOperatorPredual (H := H)) :=
  inferInstance

instance finitePredualReal : NormedSpace ℝ (finiteOperatorPredual (H := H)) :=
  inferInstance

def finiteOperatorCoefficient (x y : H) : finiteOperatorPredual (H := H) :=
  ⟨operatorCoefficient x y, Submodule.subset_span ⟨(x, y), rfl⟩⟩

omit [CompleteSpace H] in
@[simp] lemma finiteOperatorCoefficient_add_left (x z y : H) :
    finiteOperatorCoefficient (x + z) y = finiteOperatorCoefficient x y + finiteOperatorCoefficient z y := by
  apply Subtype.ext
  ext T
  exact inner_add_left _ _ _

omit [CompleteSpace H] in
@[simp] lemma finiteOperatorCoefficient_add_right (x y z : H) :
    finiteOperatorCoefficient x (y + z) = finiteOperatorCoefficient x y + finiteOperatorCoefficient x z := by
  apply Subtype.ext
  ext T
  change inner ℂ x (T (y + z)) = inner ℂ x (T y) + inner ℂ x (T z)
  simp only [map_add, inner_add_right]

omit [CompleteSpace H] in
@[simp] lemma finiteOperatorCoefficient_smul_left (c : ℂ) (x y : H) :
    finiteOperatorCoefficient (c • x) y = star c • finiteOperatorCoefficient x y := by
  apply Subtype.ext
  ext T
  change inner ℂ (c • x) (T y) = star c * inner ℂ x (T y)
  simp only [inner_smul_left, starRingEnd_apply]

omit [CompleteSpace H] in
@[simp] lemma finiteOperatorCoefficient_smul_right (c : ℂ) (x y : H) :
    finiteOperatorCoefficient x (c • y) = c • finiteOperatorCoefficient x y := by
  apply Subtype.ext
  ext T
  change inner ℂ x (T (c • y)) = c * inner ℂ x (T y)
  simp only [map_smul, inner_smul_right]

private def predualFunctionalRight (f : StrongDual ℂ (finiteOperatorPredual (H := H)))
    (x : H) : H →L[ℂ] ℂ :=
  ({ toFun := fun y => f (finiteOperatorCoefficient x y)
     map_add' := by intros; simp only [finiteOperatorCoefficient_add_right, map_add]
     map_smul' := by intros; simp only [finiteOperatorCoefficient_smul_right, map_smul,
       RingHom.id_apply] } : H →ₗ[ℂ] ℂ).mkContinuous (‖f‖ * ‖x‖) (fun y => by
    calc
      ‖f (finiteOperatorCoefficient x y)‖ ≤ ‖f‖ * ‖finiteOperatorCoefficient x y‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left
        (operatorCoefficient_norm_le x y) (norm_nonneg f)
      _ = (‖f‖ * ‖x‖) * ‖y‖ := by ring)

private def predualFunctionalForm (f : StrongDual ℂ (finiteOperatorPredual (H := H))) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  ({ toFun := predualFunctionalRight f
     map_add' := by intros; ext y; simp only [predualFunctionalRight,
       LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
       finiteOperatorCoefficient_add_left, map_add, add_apply]
     map_smul' := by intros; ext y; simp only [predualFunctionalRight,
       LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
       finiteOperatorCoefficient_smul_left, map_smul, smul_apply, starRingEnd_apply] } : H →ₗ⋆[ℂ] H →L[ℂ] ℂ).mkContinuous ‖f‖
    (fun x => by
      change ‖predualFunctionalRight f x‖ ≤ ‖f‖ * ‖x‖
      unfold predualFunctionalRight
      exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg f) (norm_nonneg x)) _)

def finitePredualOperator (f : StrongDual ℂ (finiteOperatorPredual (H := H))) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (predualFunctionalForm f)).adjoint

lemma finitePredualOperator_coefficient (f : StrongDual ℂ (finiteOperatorPredual (H := H)))
    (x y : H) : operatorCoefficient x y (finitePredualOperator f) = f (finiteOperatorCoefficient x y) := by
  change inner ℂ x ((InnerProductSpace.continuousLinearMapOfBilin
    (predualFunctionalForm f)).adjoint y) = _
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

theorem finitePredualOperator_represents (f : StrongDual ℂ (finiteOperatorPredual (H := H)))
    (ψ : finiteOperatorPredual (H := H)) : ψ.val (finitePredualOperator f) = f ψ := by
  obtain ⟨ψ, hψ⟩ := ψ
  induction hψ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨⟨x, y⟩, rfl⟩ := hψ
    exact finitePredualOperator_coefficient f x y
  | zero => change (0 : ℂ) = f 0; rw [map_zero]
  | add x y hx hy ihx ihy =>
    change (x + y) (finitePredualOperator f) = f (⟨x, hx⟩ + ⟨y, hy⟩)
    simp only [add_apply, map_add, ihx, ihy]
  | smul c x hx ih =>
    change (c • x) (finitePredualOperator f) = f (c • ⟨x, hx⟩)
    simp only [smul_apply, map_smul, ih]

theorem finitePredual_real_duality (f : StrongDual ℝ (finiteOperatorPredual (H := H))) :
    ∃ T : H →L[ℂ] H, ∀ ψ : finiteOperatorPredual (H := H), f ψ = (ψ.val T).re := by
  refine ⟨finitePredualOperator (f.extendRCLike (𝕜 := ℂ)), ?_⟩
  intro ψ
  rw [finitePredualOperator_represents]
  exact (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) f ψ).symm

end WeakPureInfiniteness

end

end OAI
