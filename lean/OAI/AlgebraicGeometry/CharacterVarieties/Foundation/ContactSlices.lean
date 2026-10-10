import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.RegularStrips
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.SurfacePresentation

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties
open scoped Classical
namespace OldContactSlice
variable {R V α : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (a : α → ℕ) (e : (α → R) ≃ₗ[R] V) (U : Submodule R V) (k : ℕ)

/-- The image of U on a NAMED old graded fiber. This definition does not choose an unrelated subspace with the same dimension. -/
def slice : Submodule R ({i // a i=k} → R) :=
  (U ⊓ framedPrefix a e (k+1)).map (framedGrade a e k)

lemma mem_slice_iff (z : {i // a i=k} → R) :
    z∈slice a e U k ↔ ∃ v, v∈U ∧ v∈framedPrefix a e (k+1) ∧ framedGrade a e k v=z := by
  simp only [slice,Submodule.mem_map,Submodule.mem_inf]
  aesop

/-- Both flag equality AND its quotient identification are used. -/
theorem invariant {f : (α → R) ≃ₗ[R] V} (h : SameFramedFlag a e f) :
    slice a e U k=slice a f U k := by
  ext z
  rw [mem_slice_iff,mem_slice_iff]
  constructor
  · rintro ⟨v,hU,hv,hz⟩
    exact ⟨v,hU,(h.1 (k+1)) ▸ hv,(h.2 k v hv).symm.trans hz⟩
  · rintro ⟨v,hU,hv,hz⟩
    have he : v∈framedPrefix a e (k+1) := (h.1 (k+1)).symm ▸ hv
    exact ⟨v,hU,he,(h.2 k v he).trans hz⟩

lemma grade_zero_iff (v : V) (hv : v∈framedPrefix a e (k+1)) :
    framedGrade a e k v=0 ↔ v∈framedPrefix a e k := by
  rcases hv with ⟨x,hx,rfl⟩
  change coordinateGrade R a k (e.symm (e x))=0 ↔ _
  rw [e.symm_apply_apply]
  constructor
  · intro hz
    refine ⟨x,?_,rfl⟩
    intro i hi
    by_cases he : a i=k
    · exact congrFun hz ⟨i,he⟩
    · exact hx i (by omega)
  · rintro ⟨y,hy,hxy⟩
    have he : y=x := e.injective hxy
    subst y
    ext i
    exact hy i.val (le_of_eq i.property.symm)

/-- The induced U map retains its inclusion in the old graded module. -/
def toSlice : ↥(U ⊓ framedPrefix a e (k+1)) →ₗ[R] slice a e U k :=
  ((framedGrade a e k).comp (U ⊓ framedPrefix a e (k+1)).subtype).codRestrict _
    (fun x => ⟨x.val,x.property,rfl⟩)

lemma toSlice_surjective : Function.Surjective (toSlice a e U k) := by
  rintro ⟨z,hz⟩
  rcases (mem_slice_iff a e U k z).mp hz with ⟨v,hu,hv,rfl⟩
  exact ⟨⟨v,hu,hv⟩,rfl⟩


theorem toSlice_ker : LinearMap.ker (toSlice a e U k)=
    (framedPrefix a e k).comap (U ⊓ framedPrefix a e (k+1)).subtype := by
  ext v
  change (toSlice a e U k) v=0 ↔ v.val∈framedPrefix a e k
  rw [← Subtype.val_inj]
  exact grade_zero_iff a e k v.val v.property.2

/-- The old adjacent interval, before any coordinate choice on U or Q. -/
def data : IntrinsicInterval.Data R V where
  previous := framedPrefix a e k
  current := framedPrefix a e (k+1)
  subsystem := U
  increasing := Submodule.map_mono (prefix_mono a (Nat.le_succ k))

def gradeMap : (data a e U k).current →ₗ[R] ({i // a i=k} → R) :=
  (framedGrade a e k).comp (data a e U k).current.subtype

lemma gradeMap_surjective : Function.Surjective (gradeMap a e U k) := by
  intro z
  let x : α → R := fun i => if h : a i=k then z ⟨i,h⟩ else 0
  have hx : x∈coordinatePrefix R a (k+1) := by
    intro i hi
    simp only [x]
    rw [dite_eq_right (by omega)]
  refine ⟨⟨e x,⟨x,hx,rfl⟩⟩,?_⟩
  change coordinateGrade R a k (e.symm (e x))=z
  rw [e.symm_apply_apply]
  ext i
  change (if h : a i.val=k then z ⟨i.val,h⟩ else 0)=z i
  simp only [dite_eq_left i.property]

lemma gradeMap_ker : (gradeMap a e U k).ker=(data a e U k).p := by
  ext v
  exact grade_zero_iff a e k v.val v.property

/-- This is the graded module identified by the old seam, not merely an isomorphic module of the same rank. The formula on representatives is literal. -/
def namedGrade : (data a e U k).G ≃ₗ[R] ({i // a i=k} → R) :=
  (Submodule.quotEquivOfEq _ _ (gradeMap_ker a e U k).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (gradeMap_surjective a e U k))

@[simp] theorem namedGrade_mk (v : (data a e U k).current) :
    namedGrade a e U k (Submodule.Quotient.mk v)=framedGrade a e k v.val := rfl

/-- The intersection grade maps onto exactly the old named submodule. -/
theorem namedGrade_subsystem :
    (data a e U k).S.map (namedGrade a e U k).toLinearMap=slice a e U k := by
  ext z
  constructor
  · rintro ⟨q,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨v.val,⟨hv,v.property⟩,rfl⟩
  · rintro ⟨v,⟨hU,hv⟩,rfl⟩
    exact ⟨Submodule.Quotient.mk (⟨v,hv⟩ : (data a e U k).current),
      ⟨⟨v,hv⟩,hU,rfl⟩,rfl⟩

/-- A canonical extraction of the U-quotient into the named old grade. -/
def namedU : (data a e U k).UG ≃ₗ[R] slice a e U k :=
  (data a e U k).uGradeEquiv.trans
    ((namedGrade a e U k).ofSubmodules _ _ (namedGrade_subsystem a e U k))

@[simp] theorem namedU_val (u : (data a e U k).UG) :
    (namedU a e U k u).val=namedGrade a e U k ((data a e U k).includeU u) := rfl

/-- The NAMED old quotient, modulo its extracted submodule, is the induced quotient-subsystem grade. -/
def namedQ : (({i // a i=k} → R) ⧸ slice a e U k) ≃ₗ[R] (data a e U k).QG :=
  (Submodule.Quotient.equiv _ _ (namedGrade a e U k)
    (namedGrade_subsystem a e U k)).symm.trans (data a e U k).qGradeEquiv

@[simp] theorem namedQ_mk (v : (data a e U k).G) :
    namedQ a e U k (Submodule.Quotient.mk (namedGrade a e U k v))=
      (data a e U k).projectQ v := by
  change (data a e U k).qGradeEquiv
    ((Submodule.Quotient.equiv _ _ (namedGrade a e U k)
      (namedGrade_subsystem a e U k)).symm
      ((Submodule.Quotient.equiv _ _ (namedGrade a e U k)
        (namedGrade_subsystem a e U k)) (Submodule.Quotient.mk v)))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl


/-- Moving the old ambient fiber moves the old subsystem with it; the named child slice itself is unchanged. This retains transports, not just ranks. -/
theorem transported {W : Type*} [AddCommGroup W] [Module R W] (t : V ≃ₗ[R] W) :
    slice a (e.trans t) (U.map t.toLinearMap) k=slice a e U k := by
  ext z
  rw [mem_slice_iff,mem_slice_iff]
  constructor
  · rintro ⟨v,⟨u,hu,rfl⟩,hv,hz⟩
    refine ⟨u,hu,?_,?_⟩
    · rcases hv with ⟨x,hx,hxv⟩
      exact ⟨x,hx,t.injective hxv⟩
    · simpa only [framedGrade,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
        LinearEquiv.trans_symm,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hz
  · rintro ⟨v,hU,⟨x,hx,hxv⟩,hz⟩
    refine ⟨t v,⟨v,hU,rfl⟩,⟨x,hx,congrArg t hxv⟩,?_⟩
    simpa only [framedGrade,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
      LinearEquiv.trans_symm,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hz

end OldContactSlice
end IntegralCharacterVarieties

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A] [Algebra R A]
variable (D : Diagram F S V arity) (P : D.Punctures R) (g : D.Solution P A)

/-- The right-hand word includes inverse CHILD transport. -/
theorem oldSeam_slice (s : S) (U : Submodule A (Fin (D.seamDim s) → A)) (k : ℕ) :
    OldContactSlice.slice (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval (algebraMap R A) g.val.val)) U k=
    OldContactSlice.slice (D.seamGrade s)
      (matrixUnitEquiv ((D.seamRight s).eval (algebraMap R A) g.val.val)) U k :=
  OldContactSlice.invariant _ _ _ _ (g.val.property (.inr s))

/-- Split, merge, continuation and interchange use their old vertex comparison. At an interchange its grade is the coarsened A⊕B grade, so this is the SAME U_* on which the complementary contact construction operates. -/
theorem oldVertex_slice (v : V)
    (U : Submodule A ((D.vertexComparison g.val.val v).Target → A)) (k : ℕ) :
    OldContactSlice.slice (D.vertexComparison g.val.val v).grade
      (D.vertexComparison g.val.val v).left.linearEquiv U k=
    OldContactSlice.slice (D.vertexComparison g.val.val v).grade
      (D.vertexComparison g.val.val v).right.linearEquiv U k :=
  OldContactSlice.invariant _ _ _ _ (g.property v)


theorem oldVertex_extraction (v : V)
    (U : Submodule A ((D.vertexComparison g.val.val v).Target → A)) (k : ℕ) :
    let c := D.vertexComparison g.val.val v
    let d := OldContactSlice.data c.grade c.left.linearEquiv U k
    let d' := OldContactSlice.data c.grade c.right.linearEquiv U k
    d.includeU.range=d.projectQ.ker ∧ d'.includeU.range=d'.projectQ.ker ∧
      d.S.map (OldContactSlice.namedGrade c.grade c.left.linearEquiv U k).toLinearMap=
        d'.S.map (OldContactSlice.namedGrade c.grade c.right.linearEquiv U k).toLinearMap := by
  dsimp only
  refine ⟨IntrinsicInterval.Data.exact_at_grade _,IntrinsicInterval.Data.exact_at_grade _,?_⟩
  rw [OldContactSlice.namedGrade_subsystem,OldContactSlice.namedGrade_subsystem]
  exact D.oldVertex_slice P g v U k
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
