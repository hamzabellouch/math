import OAI.Analysis.KadisonKastler.CornerStatePullback
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Faithful vector states implementing the corner pullbacks

Pulling a normalized corner state back by an isometry gives a normalized
faithful vector state on the original represented factor. This avoids an
extra representation assumption in the corner homogeneity application.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem isometry_sandwich_cancel (v : Algebra M) (hv : star v*v=1) (a : Algebra M) :
    star v*(v*a*star v)*v=a := by
  calc
    _ = (star v*v)*a*(star v*v) := by simp only [mul_assoc]
    _ = a := by rw [hv,one_mul,mul_one]

theorem isometry_pullback_vector_separating (v : Algebra M) (hv : star v*v=1)
    (ξ : H) (hξ : Function.Injective (algebraVectorMap M ξ)) :
    Function.Injective (algebraVectorMap M ((star v).val ξ)) := by
  intro a b hab
  have hh : (v*a*star v).val ξ=(v*b*star v).val ξ :=
    congrArg v.val hab
  have he : v*a*star v=v*b*star v := hξ hh
  have hf := congrArg (fun x : Algebra M => star v*x*v) he
  simpa only [isometry_sandwich_cancel v hv] using hf

theorem isometry_pullback_norm_sq (p : AlgebraProjection M) (v : Algebra M)
    (hvp : v*star v=p.val) (ξ : H) :
    ‖(star v).val ξ‖^2=projectionVectorWeight p ξ := by
  have h := vectorFunctional_star_mul_self ξ (star v)
  rw [star_star,hvp,vectorFunctional_projection] at h
  exact_mod_cast h.symm

theorem vectorFunctional_real_smul (ξ : H) (r : ℝ) :
    vectorFunctional (M := M) (r • ξ) = r^2 • vectorFunctional ξ := by
  ext a
  change inner ℂ (r • ξ) (a.val (r • ξ)) = r^2 • inner ℂ ξ (a.val ξ)
  rw [ContinuousLinearMap.map_smul_of_tower]
  change inner ℂ ((r : ℂ) • ξ) ((r : ℂ) • a.val ξ) = _
  rw [inner_smul_left,inner_smul_right]
  change star (r : ℂ)*((r : ℂ)*inner ℂ ξ (a.val ξ)) =
    ((r^2 : ℝ) : ℂ)*inner ℂ ξ (a.val ξ)
  simp [pow_two,mul_assoc]

theorem vectorFunctional_normalize (ξ : H) :
    vectorFunctional (M := M) (normalize ξ) = (‖ξ‖^2)⁻¹ • vectorFunctional ξ := by
  change vectorFunctional (M := M) (‖ξ‖⁻¹ • ξ) = _
  rw [vectorFunctional_real_smul,inv_pow]

theorem normalized_isometry_pullback_separating
    (v : Algebra M) (hv : star v*v=1) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ))
    (hne : (star v).val ξ≠0) :
    Function.Injective (algebraVectorMap M (normalize ((star v).val ξ))) := by
  have hinj := isometry_pullback_vector_separating v hv ξ hξ
  intro a b hab
  apply hinj
  change a.val (‖(star v).val ξ‖⁻¹ • (star v).val ξ) =
    b.val (‖(star v).val ξ‖⁻¹ • (star v).val ξ) at hab
  rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
  exact smul_right_injective H (inv_ne_zero (norm_ne_zero_iff.mpr hne)) hab

theorem vectorCornerState_pullback (p : AlgebraProjection M)
    (v : Algebra M) (hv : star v*v=1) (hvp : v*star v=p.val) (ξ : H) :
    sandwichFunctional (vectorCornerState p ξ) (star v) =
      vectorFunctional (normalize ((star v).val ξ)) := by
  have hsp : star v*p.val=star v := by
    rw [← hvp,← mul_assoc,hv,one_mul]
  have hn := isometry_pullback_norm_sq p v hvp ξ
  rw [vectorFunctional_normalize,hn]
  ext a
  rw [sandwichFunctional_apply,star_star]
  change (projectionVectorWeight p ξ)⁻¹ •
      inner ℂ (p.val.val ξ) ((v*a*star v).val (p.val.val ξ)) =
    (projectionVectorWeight p ξ)⁻¹ • inner ℂ ((star v).val ξ) (a.val ((star v).val ξ))
  congr 1
  have hs : (star v).val (p.val.val ξ)=(star v).val ξ :=
    congrArg (fun x : Algebra M => x.val ξ) hsp
  change inner ℂ (p.val.val ξ) (v.val (a.val ((star v).val (p.val.val ξ)))) = _
  rw [hs,← v.val.adjoint_inner_left]
  change inner ℂ ((star v).val (p.val.val ξ)) (a.val ((star v).val ξ)) = _
  rw [hs]

end

end KadisonKastler

end OAI
