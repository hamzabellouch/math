import OAI.Analysis.KadisonKastler.CornerProjectionRefinement

namespace OAI

/-! # Cost of removing a subprojection from a symmetric corner

For a conjugation-fixed vector, removing p from q costs at most twice
its left p-mass inside the old two-sided corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem two_projection_union_norm_sq_le {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (R : H →L[ℂ] H) (ξ : H) :
    ‖(1-(1-P)*(1-R)) ξ‖^2 ≤ ‖P ξ‖^2+‖R ξ‖^2 := by
  have he : 1-(1-P)*(1-R)=P+(1-P)*R := by
    rw [mul_sub,mul_one]
    abel
  rw [he,add_apply]
  have hi : inner ℂ (P ξ) (((1-P)*R) ξ)=0 := by
    have hs : P.adjoint=P := hP.isSelfAdjoint.star_eq
    rw [← P.adjoint_inner_right,hs]
    change inner ℂ ξ ((P*((1-P)*R)) ξ)=0
    rw [← mul_assoc,hP.mul_one_sub_self,zero_mul,zero_apply,inner_zero_right]
  have hn : ‖P ξ+((1-P)*R) ξ‖^2=‖P ξ‖^2+‖((1-P)*R) ξ‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  rw [hn]
  exact add_le_add le_rfl
    (pow_le_pow_left₀ (norm_nonneg _) (projection_apply_norm_le hP.one_sub (R ξ)) 2)

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hright in
theorem modularQuadratic_projection_fixed (q : AlgebraProjection M) (ξ : H) (hξ : J ξ=ξ) :
    J (modularQuadratic J q.val ξ)=modularQuadratic J q.val ξ := by
  have he := VonNeumannAlgebra.mem_commutant_iff.mp (hright q.val) q.val.val q.val.property
  change J (q.val.val (J (q.val.val (J ξ))))=q.val.val (J (q.val.val (J ξ)))
  rw [hξ]
  have hh := congrArg (fun T : H →L[ℂ] H => T ξ) he
  change q.val.val (J (q.val.val (J ξ)))=J (q.val.val (J (q.val.val ξ))) at hh
  simpa only [hξ] using hh.symm

include hJ hright in
theorem cornerProjection_loss_bound (q p : AlgebraProjection M) (hpq : p ≤ q)
    (ξ : H) (hξ : J ξ=ξ) :
    ‖(modularQuadratic J q.val-modularQuadratic J (q.val-p.val)) ξ‖^2 ≤
      2*‖p.val.val (modularQuadratic J q.val ξ)‖^2 := by
  let w := modularQuadratic J q.val ξ
  have hw := modularQuadratic_projection_fixed J hright q ξ hξ
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have he : modularQuadratic J (1-p.val)*modularQuadratic J q.val=
      modularQuadratic J (q.val-p.val) := by
    rw [modularQuadratic_mul J hJ hright,sub_mul,one_mul,projection_mul_of_le hpq]
  have hq : conjugationOperator J (1-p.val).val=1-conjugationOperator J p.val.val := by
    change conjugationOperator J (1-p.val.val)=_
    rw [conjugationOperator_sub,conjugationOperator_one J hJ]
  have hh : (modularQuadratic J q.val-modularQuadratic J (q.val-p.val)) ξ=
      (1-(1-p.val.val)*(1-conjugationOperator J p.val.val)) w := by
    rw [← he]
    change w-modularQuadratic J (1-p.val) w=_
    rw [modularQuadratic,hq]
    rfl
  rw [hh]
  have hn : ‖conjugationOperator J p.val.val w‖=‖p.val.val w‖ := by
    change ‖J (p.val.val (J w))‖=_
    rw [hw,J.norm_map]
  have hb := two_projection_union_norm_sq_le hp (conjugationOperator J p.val.val) w
  rw [hn] at hb
  nlinarith only [hb]

include hJ hright in
theorem cornerProjection_residual_bound (q p : AlgebraProjection M) (hpq : p ≤ q)
    (ξ : H) (hξ : J ξ=ξ) :
    ‖(1-modularQuadratic J (q.val-p.val)) ξ‖^2 ≤
      ‖(1-modularQuadratic J q.val) ξ‖^2+
      2*‖p.val.val (modularQuadratic J q.val ξ)‖^2 := by
  have hsub : IsStarProjection (q.val-p.val) := p.property.sub_of_mul_eq_left q.property
    (projection_mul_of_le hpq)
  let r : AlgebraProjection M := ⟨q.val-p.val,hsub⟩
  have hn : modularQuadratic J r.val*modularQuadratic J q.val=modularQuadratic J r.val := by
    rw [modularQuadratic_mul J hJ hright]
    change modularQuadratic J ((q.val-p.val)*q.val)=_
    rw [sub_mul,q.property.isIdempotentElem.eq,projection_mul_of_le hpq]
  have he := nested_projection_norm_sq_eq (modularQuadratic_projection J hJ hright q).one_sub
    (show (1-modularQuadratic J q.val)*(1-modularQuadratic J r.val)=
      1-modularQuadratic J q.val by
      have hn' := nested_projection_reverse (modularQuadratic_projection J hJ hright r)
        (modularQuadratic_projection J hJ hright q) hn
      rw [sub_mul,one_mul,mul_sub,mul_one,hn']
      abel) ξ
  have hd : (1-modularQuadratic J r.val)-(1-modularQuadratic J q.val)=
      modularQuadratic J q.val-modularQuadratic J r.val := by abel
  rw [hd] at he
  have hb := cornerProjection_loss_bound J hJ hright q p hpq ξ hξ
  change _+‖(modularQuadratic J q.val-modularQuadratic J (q.val-p.val)) ξ‖^2=_ at he
  linarith only [he,hb]

end

end KadisonKastler

end OAI
