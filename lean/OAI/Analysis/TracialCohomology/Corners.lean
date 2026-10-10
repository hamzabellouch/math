import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CornerComparison

namespace OAI

/-! Corners for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

def algebra : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    change p*(a+b)=a+b ∧ (a+b)*p=a+b
    simp only [mul_add,add_mul,ha,ha',hb,hb',and_self]
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    change p*(a*b)=a*b ∧ (a*b)*p=a*b
    constructor
    · rw [←mul_assoc,ha]
    · rw [mul_assoc,hb']
  smul_mem' := by
    rintro c a ⟨ha,ha'⟩
    change p*(c • a)=c • a ∧ (c • a)*p=c • a
    simp only [mul_smul_comm,smul_mul_assoc,ha,ha',and_self]
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha

instance algebra_closed : IsClosed (algebra hp : Set M) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance instOne : One (algebra hp) := ⟨⟨p,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩⟩
instance instRing : Ring (algebra hp) where
  __ := (inferInstance : NonUnitalRing (algebra hp))
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance instAlgebra : Algebra ℂ (algebra hp) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => by rw [mul_smul_comm])
instance instNormedRing : NormedRing (algebra hp) where
  __ := (inferInstance : NonUnitalNormedRing (algebra hp))
  __ := instRing hp
instance instNormedAlgebra : NormedAlgebra ℂ (algebra hp) where
  norm_smul_le c x := norm_smul_le c x
instance instCStarAlgebra : CStarAlgebra (algebra hp) where

instance instStarOrderedRing : StarOrderedRing (algebra hp) := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ algebra hp := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)

def incl : algebra hp →⋆ₙₐ[ℂ] M where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma coe_one : ((1 : algebra hp):M)=p := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma incl_apply (a : algebra hp) : incl hp a=(a:M) := rfl

end PopaCorner

namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

def compress (x : M) : algebra hp := ⟨p*x*p,by
  constructor
  · rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq]
  · rw [mul_assoc,hp.isIdempotentElem.eq]⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_norm_le (x : M) : ‖compress hp x‖ ≤ ‖x‖ := by
  change ‖p*x*p‖ ≤ ‖x‖
  calc
    _ ≤ (‖p‖*‖x‖)*‖p‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg p))
    _ ≤ (1*‖x‖)*1 := mul_le_mul (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg x)) hp.norm_le
      (norm_nonneg p) (by positivity)
    _ = ‖x‖ := by ring
end PopaCorner

open Filter Topology
open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)

def weakSpace : Submodule ℂ (WeakDual ℂ X) :=
  (algebra hp).toNonUnitalSubalgebra.toSubmodule.comap (WeakAlgebra.weakEquiv e).toLinearMap

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakSpace_closed : IsClosed (weakSpace e hp : Set (WeakDual ℂ X)) := by
  have hL := WeakAlgebra.normal_continuous e (ContinuousLinearMap.mul ℂ M p)
    ((HochschildSakai.abstract_multiplication_normal e).1 p)
  have hR := WeakAlgebra.normal_continuous e ((ContinuousLinearMap.mul ℂ M).flip p)
    ((HochschildSakai.abstract_multiplication_normal e).2 p)
  have he : (weakSpace e hp : Set (WeakDual ℂ X)) =
      {f | (WeakAlgebra.weakEquiv e).symm (p*WeakAlgebra.weakEquiv e f)=f} ∩
      {f | (WeakAlgebra.weakEquiv e).symm (WeakAlgebra.weakEquiv e f*p)=f} := by
    ext f
    change (p*WeakAlgebra.weakEquiv e f=WeakAlgebra.weakEquiv e f ∧
      WeakAlgebra.weakEquiv e f*p=WeakAlgebra.weakEquiv e f) ↔ _
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,LinearEquiv.symm_apply_eq]
  rw [he]
  exact (isClosed_eq hL continuous_id).inter (isClosed_eq hR continuous_id)

def strongEquiv : WeakSubspace.strong (weakSpace e hp) ≃ₗᵢ⋆[ℂ] algebra hp where
  toFun f := ⟨e f.val,by
    have hh := (WeakSubspace.mem_strong (weakSpace e hp) f.val).mp f.property
    exact hh⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ algebra hp
    simp⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

def predualEquiv : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)) ≃ₗᵢ⋆[ℂ] algebra hp :=
  (WeakSubspace.quotientDualEquiv (weakSpace e hp) (weakSpace_closed e hp)).trans
    (strongEquiv e hp)

omit [PartialOrder M] [StarOrderedRing M] in
lemma predualEquiv_symm_apply_mk (a : algebra hp) (z : X) :
    (predualEquiv e hp).symm a (Submodule.Quotient.mk z)=e.symm (a:M) z := by
  have hs : ∀ F : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)),
      e.symm ((predualEquiv e hp F : algebra hp):M) z = F (Submodule.Quotient.mk z) := by
    intro F
    change e.symm (e (F.comp (WeakSubspace.preannihilator (weakSpace e hp)).mkQL)) z=_
    rw [e.symm_apply_apply]
    rfl
  have hh := hs ((predualEquiv e hp).symm a)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh.symm

include e in
omit [PartialOrder M] [StarOrderedRing M] in
theorem corner_wstar : WStarAlgebra (algebra hp) :=
  ⟨⟨X ⧸ WeakSubspace.preannihilator (weakSpace e hp),inferInstance,inferInstance,
    inferInstance,⟨predualEquiv e hp⟩⟩⟩
end PopaCorner

end

end OAI
