import OAI.Analysis.KadisonKastler.ProjectionFamilySpaces

namespace OAI

/-! # The remaining corner inside a family pinching

The quadratic remainder projection is contained in the simultaneous
commutation projection, including for infinite projection families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamily_left_annihilate (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : p∈S) : p.val.val*(projectionFamilyRemainder S).val.val=0 := by
  ext x
  exact (mem_projectionFamilyRemainderSpace S _).mp
    (Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace S).toSubmodule x) p hp

theorem projectionFamily_right_annihilate (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : p∈S) : (projectionFamilyRemainder S).val.val*p.val.val=0 := by
  have he := congrArg star (projectionFamily_left_annihilate S p hp)
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  have hq : star (projectionFamilyRemainder S).val.val=(projectionFamilyRemainder S).val.val :=
    congrArg Subtype.val (projectionFamilyRemainder S).property.isSelfAdjoint.star_eq
  simpa only [star_mul,star_zero,hs,hq] using he

theorem orthogonal_modularQuadratic_annihilate
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (p q : AlgebraProjection M) (hpq : p.val.val*q.val.val=0) :
    p.val.val*modularQuadratic J q.val=0 ∧
      conjugationOperator J p.val.val*modularQuadratic J q.val=0 := by
  constructor
  · change p.val.val*(q.val.val*conjugationOperator J q.val.val)=0
    rw [← mul_assoc,hpq,zero_mul]
  · have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) q.val.val q.val.property
    change conjugationOperator J p.val.val*(q.val.val*conjugationOperator J q.val.val)=0
    rw [← mul_assoc,← hc,mul_assoc,← conjugationOperator_mul J hJ,hpq]
    have hz : conjugationOperator J (0 : H →L[ℂ] H)=0 := by ext x; exact map_zero J
    rw [hz,mul_zero]

theorem projectionFamily_quadratic_mem_commutation
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) (x : H) :
    modularQuadratic J (projectionFamilyRemainder S).val x ∈ projectionFamilyCommutationSpace J S := by
  rw [mem_projectionFamilyCommutationSpace]
  intro p hp
  have hh := orthogonal_modularQuadratic_annihilate J hJ hright p (projectionFamilyRemainder S)
    (projectionFamily_left_annihilate S p hp)
  have h1 := congrArg (fun T : H →L[ℂ] H => T x) hh.1
  have h2 := congrArg (fun T : H →L[ℂ] H => T x) hh.2
  exact h1.trans h2.symm

theorem projectionFamilyPinching_quadratic
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    projectionFamilyPinching J S*modularQuadratic J (projectionFamilyRemainder S).val=
      modularQuadratic J (projectionFamilyRemainder S).val := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (projectionFamily_quadratic_mem_commutation J hJ hright S x)

theorem projectionFamilyCommutationSpace_conjugate
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (S : Set (AlgebraProjection M)) {x : H}
    (hx : x ∈ projectionFamilyCommutationSpace J S) :
    J x ∈ projectionFamilyCommutationSpace J S := by
  rw [mem_projectionFamilyCommutationSpace] at hx ⊢
  intro p hp
  have he := congrArg J (hx p hp)
  change J (p.val.val x)=J (J (p.val.val (J x))) at he
  rw [hJ] at he
  change p.val.val (J x)=J (p.val.val (J (J x)))
  rw [hJ]
  exact he.symm

theorem projectionFamily_remainder_central
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) {x : H}
    (hx : x ∈ projectionFamilyCommutationSpace J S) :
    (projectionFamilyRemainder S).val.val x=
      conjugationOperator J (projectionFamilyRemainder S).val.val x := by
  let q := projectionFamilyRemainder S
  have haux (y : H) (hy : y ∈ projectionFamilyCommutationSpace J S) :
      conjugationOperator J q.val.val (q.val.val y)=q.val.val y := by
    have hmem : J (q.val.val y) ∈ projectionFamilyRemainderSpace S := by
      rw [mem_projectionFamilyRemainderSpace]
      intro p hp
      have hc := congrArg (fun T : H →L[ℂ] H => T y)
        (VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) q.val.val q.val.property)
      change q.val.val (conjugationOperator J p.val.val y)=
        conjugationOperator J p.val.val (q.val.val y) at hc
      have hyp := (mem_projectionFamilyCommutationSpace J S y).mp hy p hp
      have hz := congrArg (fun T : H →L[ℂ] H => T y) (projectionFamily_right_annihilate S p hp)
      change q.val.val (p.val.val y)=0 at hz
      calc
        p.val.val (J (q.val.val y)) = J (conjugationOperator J p.val.val (q.val.val y)) := by
          change _=J (J (p.val.val (J (q.val.val y))))
          rw [hJ]
        _ = J (q.val.val (conjugationOperator J p.val.val y)) := by rw [← hc]
        _ = 0 := by rw [← hyp,hz,map_zero]
    have hf : q.val.val (J (q.val.val y))=J (q.val.val y) :=
      Submodule.starProjection_eq_self_iff.mpr hmem
    change J (q.val.val (J (q.val.val y)))=q.val.val y
    rw [hf,hJ]
  have ha := haux x hx
  have hb := congrArg J (haux (J x) (projectionFamilyCommutationSpace_conjugate J hJ S hx))
  change J (J (q.val.val (J (q.val.val (J x)))))=J (q.val.val (J x)) at hb
  rw [hJ] at hb
  have hc := congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright q.val) q.val.val q.val.property)
  exact ha.symm.trans (hc.symm.trans hb)

theorem projectionFamily_remainder_mul_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) :
    (projectionFamilyRemainder S).val.val*projectionFamilyPinching J S=
      modularQuadratic J (projectionFamilyRemainder S).val := by
  let q := projectionFamilyRemainder S
  let R := projectionFamilyPinching J S
  have hRQ : R*modularQuadratic J q.val=modularQuadratic J q.val :=
    projectionFamilyPinching_quadratic J hJ hright S
  have hQR : modularQuadratic J q.val*R=modularQuadratic J q.val := by
    have he := congrArg star hRQ
    have hRs : star R=R := (projectionFamilyPinching_isProjection J S).isSelfAdjoint.star_eq
    simpa only [star_mul,hRs,
      (modularQuadratic_projection J hJ hright q).isSelfAdjoint.star_eq] using he
  ext x
  have hx : R x ∈ projectionFamilyCommutationSpace J S :=
    Submodule.starProjection_apply_mem _ _
  have hc := projectionFamily_remainder_central J hJ hright S hx
  have hi := congrArg (fun a : Algebra M => a.val (R x)) q.property.isIdempotentElem.eq
  have he : modularQuadratic J q.val (R x)=q.val.val (R x) := by
    change q.val.val (conjugationOperator J q.val.val (R x))=q.val.val (R x)
    rw [← hc]
    exact hi
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => T x) hQR)

end

end KadisonKastler

end OAI
