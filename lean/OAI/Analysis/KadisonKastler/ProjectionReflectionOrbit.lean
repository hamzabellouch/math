import OAI.Analysis.KadisonKastler.UnitaryStateDefect

namespace OAI

/-! # A reflection exchanges projection defects for vector distance

At the sum of two vectors the defect is the error term; at their difference
it is the improvement term. This is the quantitative step for state orbits.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance reflectionOrbitReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem selfAdjoint_unitary_distance_identity (U : unitary (H →L[ℂ] H))
    (hU : star (U : H →L[ℂ] H)=U) (x y : H) :
    ‖x-(U : H →L[ℂ] H) y‖^2 = ‖x-y‖^2+
      (1/4:ℝ)*‖(U : H →L[ℂ] H) (x+y)-(x+y)‖^2-
      (1/4:ℝ)*‖(U : H →L[ℂ] H) (x-y)-(x-y)‖^2 := by
  have hsym : inner ℝ ((U : H →L[ℂ] H) x) y = inner ℝ x ((U : H →L[ℂ] H) y) := by
    simp only [real_inner_eq_re_inner]
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hU]
  have hs := norm_sub_sq_real ((U : H →L[ℂ] H) (x+y)) (x+y)
  have hd := norm_sub_sq_real ((U : H →L[ℂ] H) (x-y)) (x-y)
  rw [Unitary.norm_map] at hs hd
  simp only [map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right] at hs hd
  rw [norm_sub_sq_real x ((U : H →L[ℂ] H) y),Unitary.norm_map,
    norm_sub_sq_real x y]
  conv_rhs at hs => rw [norm_add_sq_real]
  conv_rhs at hd => rw [norm_sub_sq_real]
  simp only [map_add,map_sub]
  linarith only [hs,hd,hsym,real_inner_comm ((U : H →L[ℂ] H) y) x]

def projectionOrbitReflection (p : AlgebraProjection M) : unitary (Algebra M) :=
  ⟨(2:ℂ) • p.val-1, by
    have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
    have hu := projectionReflection_unitary hp
    constructor
    · apply Subtype.ext
      exact hu.1
    · apply Subtype.ext
      exact hu.2⟩

theorem projectionOrbitReflection_star (p : AlgebraProjection M) :
    star (projectionOrbitReflection p)=projectionOrbitReflection p := by
  apply Subtype.ext
  change star ((2:ℂ) • p.val-1)=(2:ℂ) • p.val-1
  rw [star_sub,star_smul,p.property.isSelfAdjoint.star_eq,star_ofNat,star_one]

theorem projectionOrbitReflection_defect
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (p : AlgebraProjection M) (x : H) :
    ‖(modularUnitary J hJ (projectionOrbitReflection p) : H →L[ℂ] H) x-x‖ =
      2*‖centralVectorDefect J x p.val.val‖ := by
  rw [← projectionOrbitReflection_star p,
    ← centralVectorDefect_unitary_norm_eq J hJ]
  change ‖centralVectorDefect J x ((2:ℂ) • p.val.val-1)‖=_
  rw [map_sub,map_smul,centralVectorDefect_one J hJ,sub_zero,norm_smul]
  norm_num

theorem projectionOrbitReflection_distance
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (p : AlgebraProjection M) (x y : H) :
    ‖x-(modularUnitary J hJ (projectionOrbitReflection p) : H →L[ℂ] H) y‖^2 =
      ‖x-y‖^2+‖centralVectorDefect J (x+y) p.val.val‖^2-
        ‖centralVectorDefect J (x-y) p.val.val‖^2 := by
  have hstar : star (modularUnitary J hJ (projectionOrbitReflection p) : H →L[ℂ] H)=
      modularUnitary J hJ (projectionOrbitReflection p) := by
    rw [modularUnitary_coe,modularQuadratic_star J hJ hright]
    have hs := congrArg (fun u : unitary (Algebra M) => u.val)
      (projectionOrbitReflection_star p)
    rw [show star (projectionOrbitReflection p).val=(projectionOrbitReflection p).val from hs]
  rw [selfAdjoint_unitary_distance_identity _ hstar,
    projectionOrbitReflection_defect J hJ,projectionOrbitReflection_defect J hJ]
  ring

end
end KadisonKastler

end OAI
