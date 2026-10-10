import OAI.Analysis.KadisonKastler.CompleteLinearLimits

namespace OAI

/-! # The ordinary continuous bilinear map underlying a row-column bound -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- No continuity premise is required in the published correction theorem:
it follows directly from the scalar part of its Haagerup estimate. -/
def HaagerupBound.toContinuousBilinear {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) : A →L[ℂ] A →L[ℂ] A :=
  let inner (x : A) : A →L[ℂ] A := (f x).mkContinuous (c * ‖x‖) (hf.apply_norm_le x)
  let outer : A →ₗ[ℂ] A →L[ℂ] A :=
    { toFun := inner
      map_add' x y := by ext z; exact congrArg (fun D : A →ₗ[ℂ] A => D z) (f.map_add x y)
      map_smul' r x := by ext z; exact congrArg (fun D : A →ₗ[ℂ] A => D z) (f.map_smul r x) }
  outer.mkContinuous c (fun x => ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hc (norm_nonneg x)) (hf.apply_norm_le x))

@[simp] theorem HaagerupBound.toContinuousBilinear_apply
    {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ} (hf : HaagerupBound f c) (hc : 0 ≤ c) (x y : A) :
    hf.toContinuousBilinear hc x y = f x y := rfl

end

end KadisonKastler

end OAI
