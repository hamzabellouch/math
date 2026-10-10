import OAI.Algebra.Finitistic.Localization.VectorComplexFormality
import OAI.Algebra.Finitistic.Localization.IdempotentImageEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents HomologicalComplex
namespace LittleFinitistic.VectorComplexFormality
open FiniteProjectiveHomotopy QuadraticEncoding
universe u v
variable {k : Type u} [Field k]

lemma zeroDifferential_homotopy_eq {C D : CochainComplex (ModuleCat.{v} k) ℤ}
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) (f g : C ⟶ D)
    (h : (HomotopyCategory.quotient _ _).map f = (HomotopyCategory.quotient _ _).map g) : f=g := by
  ext i : 1
  have h' := (HomotopyCategory.homotopyOfEq f g h).comm i
  simpa [dNext, prevD, hC, hD] using h'

lemma zeroDifferential_idempotents_split (T : K.{u,v} k)
    (hT : ∀ i j, T.obj.as.d i j = 0) (p : T ⟶ T) (hp : p ≫ p=p) :
    ∃ (I : K.{u,v} k) (ι : I ⟶ T) (π : T ⟶ I), ι ≫ π = 𝟙 I ∧ π ≫ ι = p := by
  let C := T.obj.as
  let q := HomotopyCategory.quotient (ModuleCat.{v} k) (.up ℤ)
  let J := inclusion k
  obtain ⟨f,hf⟩ := q.map_surjective (J.map p)
  have hff : f ≫ f=f := zeroDifferential_homotopy_eq hT hT _ _ (by
    erw [q.map_comp, hf, ← J.map_comp, hp])
  have hi (i : ℤ) : (f.f i).hom * (f.f i).hom = (f.f i).hom := by
    exact congrArg (fun g => (g.f i).hom) hff
  let V (i : ℤ) : ModuleCat.{v} k := ModuleCat.of k (LinearMap.range (f.f i).hom)
  let D := zeroComplex V
  let inc : D ⟶ C := {
    f := fun i => imageInclusion (f.f i).hom
    comm' := fun i j _ => by simp [D, zeroComplex, hT, C] }
  let pr : C ⟶ D := {
    f := fun i => imageProjection (f.f i).hom
    comm' := fun i j _ => by simp [D, zeroComplex, hT, C] }
  have hip : inc ≫ pr = 𝟙 D := by
    ext i : 1
    exact image_inclusion_projection (f.f i).hom (hi i)
  have hpi : pr ≫ inc = f := by
    ext i : 1
    exact image_projection_inclusion (f.f i).hom
  have hD : ComplexProperty k D := by
    obtain ⟨⟨a,b,hb⟩,hfin⟩ := T.property
    constructor
    · refine ⟨a,b,fun i hi => ?_⟩
      have hm : Mono (imageInclusion (f.f i).hom) := by
        rw [ModuleCat.mono_iff_injective]
        exact Submodule.subtype_injective _
      exact @IsZero.of_mono (ModuleCat k) _ _ _ _
        (imageInclusion (f.f i).hom) hm (hb i hi)
    · intro i
      have := (hfin i).1
      refine ⟨?_,ModuleCat.projective_of_categoryTheory_projective _⟩
      exact Module.Finite.of_injective (LinearMap.range (f.f i).hom).subtype
        (Submodule.subtype_injective _)
  let I : K.{u,v} k := ⟨q.obj D,hD⟩
  refine ⟨I,J.preimage (q.map inc),J.preimage (q.map pr),?_,?_⟩
  · apply J.map_injective
    rw [J.map_comp, J.map_id]
    erw [Functor.map_preimage, Functor.map_preimage]
    exact (q.map_comp inc pr).symm.trans ((congrArg q.map hip).trans (q.map_id D))
  · apply J.map_injective
    rw [J.map_comp]
    erw [Functor.map_preimage, Functor.map_preimage]
    exact (q.map_comp pr inc).symm.trans ((congrArg q.map hpi).trans hf)

/-- Bounded finite-dimensional homotopy complexes split every idempotent. -/
instance finiteVectorHomotopyIdempotentComplete : IsIdempotentComplete (K.{u,v} k) where
  idempotents_split T p hp := by
    let e := formalityIso T
    let p' := e.hom ≫ p ≫ e.inv
    have hp' : p' ≫ p'=p' := by
      dsimp [p']
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc p p, hp]
    have hz : ∀ i j, (zeroHomologyK T).obj.as.d i j = 0 := fun _ _ => rfl
    exact split_imp_of_iso e p' p (by simp [p',Category.assoc])
      (zeroDifferential_idempotents_split (zeroHomologyK T) hz p' hp')

/-- The actual bounded finite-dimensional derived target is idempotent complete. -/
instance finiteVectorDerivedIdempotentComplete :
    IsIdempotentComplete (FiniteVectorDerived.{u,v} (k := k)) :=
  CategoryTheory.Idempotents.Equivalence.isIdempotentComplete (boundedDerivedEquivalence k) inferInstance
end LittleFinitistic.VectorComplexFormality

end

end OAI
