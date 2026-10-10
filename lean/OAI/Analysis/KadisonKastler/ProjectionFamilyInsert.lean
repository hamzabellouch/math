import OAI.Analysis.KadisonKastler.ProjectionFamilyCut

namespace OAI

/-! # The remaining corner after one additional projection -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem mem_projectionFamilyRemainderSpace_insert (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (x : H) :
    x ∈ projectionFamilyRemainderSpace (insert p S) ↔
      x ∈ projectionFamilyRemainderSpace S ∧ p.val.val x=0 := by
  simp only [mem_projectionFamilyRemainderSpace,Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm

theorem mem_projectionFamilyCommutationSpace_insert (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) (p : AlgebraProjection M) (x : H) :
    x ∈ projectionFamilyCommutationSpace J (insert p S) ↔
      x ∈ projectionFamilyCommutationSpace J S ∧ p.val.val x=conjugationOperator J p.val.val x := by
  simp only [mem_projectionFamilyCommutationSpace,Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm

theorem projectionFamilyRemainder_insert (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hpq : p≤projectionFamilyRemainder S) :
    (projectionFamilyRemainder (insert p S)).val=(projectionFamilyRemainder S).val-p.val := by
  let q := projectionFamilyRemainder S
  let r := AlgebraProjection.remainder p q hpq
  let q' := projectionFamilyRemainder (insert p S)
  have hrq : q.val.val*r.val.val=r.val.val :=
    congrArg Subtype.val (AlgebraProjection.remainder_le p q hpq)
  have hpr : p.val.val*r.val.val=0 :=
    congrArg Subtype.val (AlgebraProjection.remainder_orthogonal p q hpq)
  have hqr : q'.val.val*r.val.val=r.val.val := by
    ext x
    change (projectionFamilyRemainderSpace (insert p S)).toSubmodule.starProjection
      (r.val.val x)=r.val.val x
    apply Submodule.starProjection_eq_self_iff.mpr
    change r.val.val x ∈ projectionFamilyRemainderSpace (insert p S)
    rw [mem_projectionFamilyRemainderSpace_insert]
    constructor
    · have he := congrArg (fun T : H →L[ℂ] H => T x) hrq
      change q.val.val (r.val.val x)=r.val.val x at he
      rw [← he]
      exact Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace S).toSubmodule _
    · exact congrArg (fun T : H →L[ℂ] H => T x) hpr
  have hrq' : r.val.val*q'.val.val=q'.val.val := by
    ext x
    have hx := (mem_projectionFamilyRemainderSpace_insert S p _).mp
      (Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace (insert p S)).toSubmodule x)
    have he : q.val.val (q'.val.val x)=q'.val.val x :=
      Submodule.starProjection_eq_self_iff.mpr hx.1
    have hz : p.val.val (q'.val.val x)=0 := hx.2
    change q.val.val (q'.val.val x)-p.val.val (q'.val.val x)=q'.val.val x
    rw [he,hz,sub_zero]
  have hrq'' : r.val.val*q'.val.val=r.val.val := by
    have he := congrArg star hqr
    have hsr : star r.val.val=r.val.val := congrArg Subtype.val r.property.isSelfAdjoint.star_eq
    have hsq : star q'.val.val=q'.val.val := congrArg Subtype.val q'.property.isSelfAdjoint.star_eq
    simpa only [star_mul,hsr,hsq] using he
  exact Subtype.ext (hrq'.symm.trans hrq'')

end

end KadisonKastler

end OAI
