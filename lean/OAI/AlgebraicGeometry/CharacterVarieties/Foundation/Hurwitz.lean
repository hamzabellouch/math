import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.CornerHolonomy
import Mathlib.GroupTheory.FreeGroup.Basic

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

/-- Only the ordered boundary enumeration is changed. Every side, corner, seam, genus and facet
remains the old one. -/
def reorderBoundary (σ : ∀ f,Equiv.Perm (Fin (D.boundaryCount f))) : Diagram F S V arity where
  ports := D.ports
  rank := D.rank
  seamRank := D.seamRank
  genus := D.genus
  boundaryCount := D.boundaryCount
  boundaryLength f b := D.boundaryLength f (σ f b)
  boundaryPositive f b := D.boundaryPositive f (σ f b)
  boundarySide := (Equiv.sigmaCongrRight (fun f =>
    Equiv.sigmaCongr (σ f) (fun _ => Equiv.refl _))).trans D.boundarySide
  boundaryFacet f b i := D.boundaryFacet f (σ f b) i
  boundaryNext f b i := D.boundaryNext f (σ f b) i

variable {R : Type*} [CommRing R]

/-- This producer merely transfers the identical named matrix coordinates; the noncommutative re-
framing is performed before this transfer. -/
def reorderGenerators (σ : ∀ f,Equiv.Perm (Fin (D.boundaryCount f)))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ) :
    (e : (D.reorderBoundary σ).Generator) →
      (Matrix (Fin ((D.reorderBoundary σ).generatorRank e))
        (Fin ((D.reorderBoundary σ).generatorRank e)) R)ˣ
  | .side a => g (.side a)
  | .frame s b => g (.frame s b)
  | .handle f k b => g (.handle f k b)

lemma reorder_vertexComparison (σ : ∀ f,Equiv.Perm (Fin (D.boundaryCount f)))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (v : V) : (D.reorderBoundary σ).vertexComparison (D.reorderGenerators σ g) v=
      D.vertexComparison g v := rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram

/- The based reorderings are changes of free generators, with inverses. -/
namespace IntegralCharacterVarieties.SurfaceSurgery.Hurwitz
open scoped Classical
variable {I : Type*}

def negative (a b : I) : FreeGroup I →* FreeGroup I :=
  FreeGroup.lift (fun i => if i=b then (FreeGroup.of a)⁻¹*FreeGroup.of b*FreeGroup.of a
    else FreeGroup.of i)
def positive (a b : I) : FreeGroup I →* FreeGroup I :=
  FreeGroup.lift (fun i => if i=b then FreeGroup.of a*FreeGroup.of b*(FreeGroup.of a)⁻¹
    else FreeGroup.of i)

lemma positive_negative (a b : I) (hab : a≠b) :
    (positive a b).comp (negative a b)=MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i=b
  · subst i
    simp [positive,negative,hab]
    group
  · simp [positive,negative,hi]

lemma negative_positive (a b : I) (hab : a≠b) :
    (negative a b).comp (positive a b)=MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i=b
  · subst i
    simp [positive,negative,hab]
    group
  · simp [positive,negative,hi]

/-- The elementary Hurwitz automorphism fixes every other free generator. -/
def swapAutomorphism (a b : I) (hab : a≠b) : FreeGroup I ≃* FreeGroup I where
  toFun := negative a b
  invFun := positive a b
  left_inv w := DFunLike.congr_fun (positive_negative a b hab) w
  right_inv w := DFunLike.congr_fun (negative_positive a b hab) w
  map_mul' := map_mul _

@[simp] lemma swapAutomorphism_of (a b : I) (hab : a≠b) (i : I) :
    swapAutomorphism a b hab (FreeGroup.of i)=
      if i=b then (FreeGroup.of a)⁻¹*FreeGroup.of b*FreeGroup.of a else FreeGroup.of i :=
  FreeGroup.lift_apply_of

/-- A finite boundary enumeration change together with an invertible word substitution. Product
preservation is NOT the only stored certificate. -/
structure BasedPermutation (l m : List I) where
  automorphism : FreeGroup I ≃* FreeGroup I
  paths : I → FreeGroup I
  generator : ∀ i, automorphism (FreeGroup.of i)=paths i*FreeGroup.of i*(paths i)⁻¹
  product : automorphism (m.map FreeGroup.of).prod=(l.map FreeGroup.of).prod
  fixed : ∀ i,i∉l → automorphism (FreeGroup.of i)=FreeGroup.of i

/-- Obtained solely from the permutation of distinct circle labels. -/
theorem basedPermutation_exists {l m : List I} (hp : l.Perm m) (hn : l.Nodup) :
    Nonempty (BasedPermutation l m) := by
  classical
  induction hp with
  | nil =>
    refine ⟨⟨MulEquiv.refl _,fun _ => 1,?_,?_,?_⟩⟩
    · intro i; simp
    · simp
    · intro i hi; rfl
  | @cons a l m hp ih =>
    obtain ⟨Q⟩ := ih (List.nodup_cons.mp hn).2
    refine ⟨⟨Q.automorphism,Q.paths,Q.generator,?_,?_⟩⟩
    · simp only [List.map_cons,List.prod_cons,map_mul,
        Q.fixed a (List.nodup_cons.mp hn).1,Q.product]
    · intro i hi
      exact Q.fixed i (fun h => hi (by simp [h]))
  | swap a b l =>
    have hba : b≠a := by
      intro h
      exact (List.nodup_cons.mp hn).1 (by simp [h])
    have hbl : b∉l := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    let e := swapAutomorphism a b hba.symm
    refine ⟨⟨e,fun i => if i=b then (FreeGroup.of a)⁻¹ else 1,?_,?_,?_⟩⟩
    · intro i
      by_cases hi : i=b
      · subst i; simp [e]
      · simp [e,hi]
    · have he : l.map (fun i => e (FreeGroup.of i))=l.map FreeGroup.of := by
        apply List.map_congr_left
        intro i hi
        have hib : i≠b := by rintro rfl; exact hbl hi
        simp [e,hib]
      simp only [List.map_cons,List.prod_cons,map_mul,map_list_prod,List.map_map,
        Function.comp_def,he]
      simp only [e,swapAutomorphism_of,ite_eq_right hba.symm]
      simp only [↓reduceIte]
      group
    · intro i hi
      have hib : i≠b := by rintro rfl; exact hi (by simp)
      simp [e,hib]
  | @trans l m n hp hq ihp ihq =>
    obtain ⟨P⟩ := ihp hn
    obtain ⟨Q⟩ := ihq (hp.nodup_iff.mp hn)
    refine ⟨⟨Q.automorphism.trans P.automorphism,
      fun i => P.automorphism (Q.paths i)*P.paths i,?_,?_,?_⟩⟩
    · intro i
      simp only [MulEquiv.trans_apply,Q.generator,map_mul,map_inv,P.generator]
      group
    · rw [MulEquiv.trans_apply,Q.product,P.product]
    · intro i hi
      have him : i∉m := fun h => hi (hp.mem_iff.mpr h)
      rw [MulEquiv.trans_apply,Q.fixed i him,P.fixed i hi]

section Evaluation
variable {H : Type*} [Group H]

/-- Precomposition by the free-group automorphism, with its inverse. This works for full-ring matrix
groups, not only for complex points. -/
def change (e : FreeGroup I ≃* FreeGroup I) (f : I → H) : I → H :=
  fun i => (FreeGroup.lift f) (e (FreeGroup.of i))

lemma lift_change (e : FreeGroup I ≃* FreeGroup I) (f : I → H) :
    FreeGroup.lift (change e f)=(FreeGroup.lift f).comp e.toMonoidHom := by
  apply FreeGroup.ext_hom
  intro i
  simp only [FreeGroup.lift_apply_of,MonoidHom.comp_apply,change]
  rfl

def evaluationEquiv (e : FreeGroup I ≃* FreeGroup I) : (I → H) ≃ (I → H) where
  toFun := change e
  invFun := change e.symm
  left_inv f := by
    funext i
    change (FreeGroup.lift (change e f)) (e.symm (FreeGroup.of i))=f i
    rw [lift_change]
    simp
  right_inv f := by
    funext i
    change (FreeGroup.lift (change e.symm f)) (e (FreeGroup.of i))=f i
    rw [lift_change]
    simp

lemma BasedPermutation.generator_eval {l m : List I} (P : BasedPermutation l m)
    (f : I → H) (i : I) :
    change P.automorphism f i=(FreeGroup.lift f) (P.paths i)*f i*
      ((FreeGroup.lift f) (P.paths i))⁻¹ := by
  simp only [change,P.generator,map_mul,map_inv,FreeGroup.lift_apply_of]

lemma BasedPermutation.product_eval {l m : List I} (P : BasedPermutation l m)
    (f : I → H) :
    (m.map (change P.automorphism f)).prod=(l.map f).prod := by
  have h := congrArg (FreeGroup.lift f) P.product
  simp only [map_list_prod,List.map_map,Function.comp_def,FreeGroup.lift_apply_of] at h
  exact h

lemma BasedPermutation.inverse_generator {l m : List I} (P : BasedPermutation l m) (i : I) :
    P.automorphism.symm (FreeGroup.of i)=
      (P.automorphism.symm (P.paths i))⁻¹*FreeGroup.of i*P.automorphism.symm (P.paths i) := by
  apply P.automorphism.injective
  simp only [map_mul,map_inv,MulEquiv.apply_symm_apply,P.generator]
  group

lemma inverse_evaluation_path (e : FreeGroup I ≃* FreeGroup I) (f : I → H) (z : FreeGroup I) :
    (FreeGroup.lift (change e f)) (e.symm z)=(FreeGroup.lift f) z := by
  rw [lift_change]
  simp
end Evaluation

/-- A fixed presentation automorphism for each finite boundary permutation. -/
def finPresentation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    BasedPermutation (List.ofFn (fun i : Fin n => i)) (List.ofFn σ) := by
  have hn : (List.ofFn (fun i : Fin n => i)).Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hm : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hp : (List.ofFn (fun i : Fin n => i)).Perm (List.ofFn σ) := by
    apply (List.perm_ext_iff_of_nodup hn hm).mpr
    intro a
    simp only [List.mem_ofFn]
    exact ⟨fun _ => σ.surjective a,fun _ => ⟨a,rfl⟩⟩
  exact Classical.choice (basedPermutation_exists hp hn)

lemma finPresentation_spec {n : ℕ} (σ : Equiv.Perm (Fin n)) {H : Type*} [Group H]
    (f : Fin n → H) :
    (List.ofFn (fun b => (FreeGroup.lift f) ((finPresentation σ).paths (σ b))*f (σ b)*
      ((FreeGroup.lift f) ((finPresentation σ).paths (σ b)))⁻¹)).prod=(List.ofFn f).prod := by
  have h := (finPresentation σ).product_eval f
  simpa only [BasedPermutation.generator_eval,List.map_ofFn,Function.comp_def] using h

end IntegralCharacterVarieties.SurfaceSurgery.Hurwitz

end

end OAI
