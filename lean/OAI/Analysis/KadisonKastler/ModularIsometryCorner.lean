import OAI.Analysis.KadisonKastler.CornerProjectionRefinement
import OAI.Analysis.KadisonKastler.PositiveConeQuadraticSupport

namespace OAI

/-! # Isometric coordinates in a two-sided modular corner

An algebra isometry induces an isometry on the Hilbert space by `v J v J`.
Projection sandwiches intertwine both left and right actions, preserving
the commutator norms used in projection refinement.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

def isometryProjectionImage (v : Algebra M) (hv : star v*v=1) (p : AlgebraProjection M) :
    AlgebraProjection M := ⟨v*p.val*star v, by
  constructor
  · change (v*p.val*star v)*(v*p.val*star v)=v*p.val*star v
    calc
      _ = v*(p.val*(star v*v)*p.val)*star v := by noncomm_ring
      _ = _ := by rw [hv,mul_one,p.property.isIdempotentElem.eq]
  · change star (v*p.val*star v)=v*p.val*star v
    simp only [star_mul,star_star,p.property.isSelfAdjoint.star_eq,mul_assoc]⟩

theorem isometryProjectionImage_nonzero (v : Algebra M) (hv : star v*v=1)
    (p : AlgebraProjection M) (hp : p.val≠0) : (isometryProjectionImage v hv p).val≠0 := by
  intro hz
  have he := congrArg (fun a : Algebra M => star v*a*v) hz
  change star v*(v*p.val*star v)*v=star v*0*v at he
  have hcancel : star v*(v*p.val*star v)*v=p.val := by
    calc
      _ = (star v*v)*p.val*(star v*v) := by noncomm_ring
      _ = _ := by rw [hv,one_mul,mul_one]
  rw [hcancel,mul_zero,zero_mul] at he
  exact hp he

theorem isometryProjectionImage_le (v : Algebra M) (hv : star v*v=1)
    (q p : AlgebraProjection M) (hq : v*star v=q.val) :
    isometryProjectionImage v hv p ≤ q := by
  change q.val*(v*p.val*star v)=v*p.val*star v
  rw [← hq]
  calc
    _ = v*(star v*v)*p.val*star v := by noncomm_ring
    _ = _ := by rw [hv,mul_one]

include hJ in
theorem modularQuadratic_one : modularQuadratic (M := M) J 1=1 := by
  change (1 : H →L[ℂ] H)*conjugationOperator J 1=1
  rw [conjugationOperator_one J hJ,one_mul]

include hJ hright in
theorem modularQuadratic_isometry (v : Algebra M) (hv : star v*v=1) :
    Isometry (modularQuadratic J v) := by
  apply (modularQuadratic J v).isometry_iff_adjoint_comp_self.mpr
  change star (modularQuadratic J v)*modularQuadratic J v=1
  rw [modularQuadratic_star J hJ hright,modularQuadratic_mul J hJ hright,
    hv,modularQuadratic_one J hJ]

include hJ hright in
theorem modularQuadratic_conjugation (v : Algebra M) :
    conjugationOperator J (modularQuadratic J v)=modularQuadratic J v := by
  change conjugationOperator J (v.val*conjugationOperator J v.val)=
    v.val*conjugationOperator J v.val
  rw [conjugationOperator_mul J hJ,conjugationOperator_twice J hJ]
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (hright v) v.val v.property).symm

include hJ hright in
theorem modularQuadratic_fixed (v : Algebra M) {ξ : H} (hξ : J ξ=ξ) :
    J (modularQuadratic J v ξ)=modularQuadratic J v ξ := by
  have he := congrArg (fun T : H →L[ℂ] H => T ξ) (modularQuadratic_conjugation J hJ hright v)
  change J (modularQuadratic J v (J ξ))=modularQuadratic J v ξ at he
  rwa [hξ] at he

include hright in
theorem isometry_sandwich_modular_left (v a : Algebra M) (hv : star v*v=1) :
    (v*a*star v).val*modularQuadratic J v=modularQuadratic J v*a.val := by
  have hv' : star v.val*v.val=1 := congrArg Subtype.val hv
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright v) a.val a.property
  change (v.val*a.val*star v.val)*(v.val*conjugationOperator J v.val)=
    (v.val*conjugationOperator J v.val)*a.val
  calc
    _ = v.val*a.val*(star v.val*v.val)*conjugationOperator J v.val := by
      noncomm_ring
    _ = v.val*(a.val*conjugationOperator J v.val) := by rw [hv',mul_one,mul_assoc]
    _ = _ := by rw [hc,mul_assoc]

include hJ hright in
theorem isometry_sandwich_modular_right (v a : Algebra M) (hv : star v*v=1) :
    conjugationOperator J (v*a*star v).val*modularQuadratic J v=
      modularQuadratic J v*conjugationOperator J a.val := by
  have he := congrArg (conjugationOperator J) (isometry_sandwich_modular_left J hright v a hv)
  simpa only [conjugationOperator_mul J hJ,modularQuadratic_conjugation J hJ hright] using he

include hJ hright in
theorem isometry_sandwich_modular_defect (v a : Algebra M) (hv : star v*v=1) (ξ : H) :
    centralVectorDefect J (modularQuadratic J v ξ) (v*a*star v).val=
      modularQuadratic J v (centralVectorDefect J ξ a.val) := by
  rw [centralVectorDefect_apply,centralVectorDefect_apply]
  have hs : star (v*a*star v)=v*star a*star v := by simp only [star_mul,star_star,mul_assoc]
  change ((v*a*star v).val-conjugationOperator J (star (v*a*star v)).val)
    (modularQuadratic J v ξ)=modularQuadratic J v ((a.val-conjugationOperator J (star a).val) ξ)
  rw [hs]
  have he : ((v*a*star v).val-conjugationOperator J (v*star a*star v).val)*
      modularQuadratic J v=modularQuadratic J v*(a.val-conjugationOperator J (star a).val) := by
    rw [sub_mul,mul_sub,isometry_sandwich_modular_left J hright v a hv,
      isometry_sandwich_modular_right J hJ hright v (star a) hv]
  exact congrArg (fun T : H →L[ℂ] H => T ξ) he

include hJ hright in
theorem isometry_sandwich_modular_defect_norm (v a : Algebra M) (hv : star v*v=1) (ξ : H) :
    ‖centralVectorDefect J (modularQuadratic J v ξ) (v*a*star v).val‖=
      ‖centralVectorDefect J ξ a.val‖ := by
  rw [isometry_sandwich_modular_defect J hJ hright v a hv]
  exact (modularQuadratic_isometry J hJ hright v hv).norm_map_of_map_zero (map_zero _) _

include hJ hright in
theorem isometry_sandwich_modular_left_norm (v a : Algebra M) (hv : star v*v=1) (ξ : H) :
    ‖(v*a*star v).val (modularQuadratic J v ξ)‖=‖a.val ξ‖ := by
  have he := congrArg (fun T : H →L[ℂ] H => T ξ)
    (isometry_sandwich_modular_left J hright v a hv)
  change (v*a*star v).val (modularQuadratic J v ξ)=modularQuadratic J v (a.val ξ) at he
  rw [he]
  exact (modularQuadratic_isometry J hJ hright v hv).norm_map_of_map_zero (map_zero _) _

end

end KadisonKastler

end OAI
