import OAI.Analysis.KadisonKastler.AsymptoticCentralizer
import OAI.Analysis.FactorGeneration.LocalizedStates

namespace OAI

/-! # Vector centrality controls the predual state commutator -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def vectorStateCommutator (ξ : H) (a : Algebra M) : Algebra M →L[ℂ] ℂ :=
  (vectorFunctional ξ).comp
    (ContinuousLinearMap.mul ℂ (Algebra M) a - (ContinuousLinearMap.mul ℂ (Algebra M)).flip a)

theorem vectorStateCommutator_defect_identity
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ a b =
      inner ℂ (centralVectorDefect J ξ (star a).val) (b.val ξ) -
        inner ℂ ξ (b.val (centralVectorDefect J ξ a.val)) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star a)) b.val b.property
  have hs : (conjugationOperator J a.val).adjoint = conjugationOperator J (star a).val :=
    (conjugationOperator_star J hJ a.val).symm
  have hm : inner ℂ (conjugationOperator J a.val ξ) (b.val ξ) =
      inner ℂ ξ (b.val (conjugationOperator J (star a).val ξ)) := by
    rw [← ContinuousLinearMap.adjoint_inner_right,hs]
    exact congrArg (inner ℂ ξ) (congrArg (fun T : H →L[ℂ] H => T ξ) hc.symm)
  have ha : inner ℂ (star a.val ξ) (b.val ξ) = inner ℂ ξ (a.val (b.val ξ)) := by
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  simp only [StarMemClass.coe_star] at hm
  change inner ℂ ξ (a.val (b.val ξ) - b.val (a.val ξ)) = _
  simp only [centralVectorDefect_apply,StarMemClass.coe_star,star_star,
    map_sub,inner_sub_left,inner_sub_right]
  rw [ha,hm]
  abel

theorem vectorStateCommutator_norm_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) (a : Algebra M) :
    ‖vectorStateCommutator ξ a‖ ≤ 2 * ‖ξ‖ * ‖centralVectorDefect J ξ a.val‖ := by
  apply (vectorStateCommutator ξ a).opNorm_le_bound
    (M := 2 * ‖ξ‖ * ‖centralVectorDefect J ξ a.val‖) (by positivity)
  intro b
  rw [vectorStateCommutator_defect_identity J hJ hright]
  calc
    _ ≤ ‖inner ℂ (centralVectorDefect J ξ (star a).val) (b.val ξ)‖ +
        ‖inner ℂ ξ (b.val (centralVectorDefect J ξ a.val))‖ := norm_sub_le _ _
    _ ≤ ‖centralVectorDefect J ξ (star a).val‖ * ‖b.val ξ‖ +
        ‖ξ‖ * ‖b.val (centralVectorDefect J ξ a.val)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖centralVectorDefect J ξ (star a).val‖ * (‖b.val‖ * ‖ξ‖) +
        ‖ξ‖ * (‖b.val‖ * ‖centralVectorDefect J ξ a.val‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (b.val.le_opNorm ξ) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (b.val.le_opNorm _) (norm_nonneg _))
    _ = _ := by
      rw [StarMemClass.coe_star,centralVectorDefect_star_norm J hJ ξ hξ]
      change _ = _ * ‖b.val‖
      ring

theorem AsymptoticallyCentral.state_commutator
    {J : H ≃ₗᵢ⋆[ℂ] H} (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    {ξ : H} (hξ : J ξ = ξ) {x : BoundedSequence (Algebra M)}
    (hx : AsymptoticallyCentral J ξ x) :
    Tendsto (fun n => ‖vectorStateCommutator ξ (x n)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => vectorStateCommutator_norm_le J hJ hright ξ hξ (x n))
  simpa only [mul_zero] using hx.const_mul (2 * ‖ξ‖)

end

end KadisonKastler

end OAI
