import OAI.Analysis.KadisonKastler.CornerProjectionRefinement

namespace OAI

/-! # Adding one cut to a partial pinching

Already selected orthogonal corners are left fixed. Refining the remaining
corner increases the residual squared norm by exactly the local commutator
energy. This is the additive identity used by the maximal-family argument.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem orthogonal_projection_mul_reverse {A B : H →L[ℂ] H}
    (hA : IsStarProjection A) (hB : IsStarProjection B) (hAB : A*B=0) : B*A=0 := by
  have he := congrArg star hAB
  simpa only [star_mul,hA.isSelfAdjoint.star_eq,hB.isSelfAdjoint.star_eq,star_zero] using he

theorem orthogonal_sum_nested {A B C : H →L[ℂ] H}
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hAB : A*B=0) (hCB : C*B=C) : (A+C)*(A+B)=A+C := by
  have hBA := orthogonal_projection_mul_reverse hA hB hAB
  have hCA : C*A=0 := by
    calc
      _ = (C*B)*A := by rw [hCB]
      _ = 0 := by rw [mul_assoc,hBA,mul_zero]
  rw [add_mul,mul_add,mul_add,hA.isIdempotentElem.eq,hAB,hCA,hCB,add_zero,zero_add]

theorem nested_projection_residual_energy {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P*R=P) (ξ : H) :
    ‖(1-P) ξ‖^2=‖(1-R) ξ‖^2+‖(R-P) ξ‖^2 := by
  have hRP := nested_projection_reverse hP hR hPR
  have hn : (1-R)*(1-P)=1-R := by
    rw [sub_mul,one_mul,mul_sub,mul_one,hRP]
    abel
  have he := nested_projection_norm_sq_eq hR.one_sub hn ξ
  have hd : (1-P)-(1-R)=R-P := by abel
  rw [hd] at he
  exact he.symm

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem partialPinching_refinement_isProjection (A : H →L[ℂ] H)
    (hA : IsStarProjection A) (q p : AlgebraProjection M) (hpq : p ≤ q)
    (hAq : A*modularQuadratic J q.val=0) :
    IsStarProjection (A+refinedCornerProjection J q p) := by
  apply hA.add (refinedCornerProjection_isProjection J hJ hright q p hpq)
  calc
    A*refinedCornerProjection J q p =
        A*(modularQuadratic J q.val*pairedProjectionCut p.val.val
          (conjugationOperator J p.val.val)) := by
      rw [refinedCornerProjection_mul_left J hJ hright q p hpq]
    _ = 0 := by rw [← mul_assoc,hAq,zero_mul]

include hJ hright in
theorem partialPinching_refinement_energy (A : H →L[ℂ] H)
    (hA : IsStarProjection A) (q p : AlgebraProjection M) (hpq : p ≤ q)
    (hAq : A*modularQuadratic J q.val=0) (ξ : H) :
    ‖(1-(A+refinedCornerProjection J q p)) ξ‖^2 =
      ‖(1-(A+modularQuadratic J q.val)) ξ‖^2+
      ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖^2 := by
  have hq := modularQuadratic_projection J hJ hright q
  have he := nested_projection_residual_energy
    (partialPinching_refinement_isProjection J hJ hright A hA q p hpq hAq)
    (hA.add hq hAq)
    (orthogonal_sum_nested hA hq hAq (refinedCornerProjection_nested J hJ hright q p hpq)) ξ
  have hd : (A+modularQuadratic J q.val)-(A+refinedCornerProjection J q p)=
      modularQuadratic J q.val-refinedCornerProjection J q p := by abel
  rwa [hd,refinedCornerProjection_discarded_norm J hJ hright q p hpq] at he

end

end KadisonKastler

end OAI
