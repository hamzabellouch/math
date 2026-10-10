import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.Hurwitz

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {A : Type*} [CommRing A] {n : ℕ}
lemma unit_injective : Function.Injective (unit (R:=A) (α:=Fin n)) := by
  intro x y h
  apply Units.ext
  exact congrArg MatrixIso.val h
end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open HomTransport OccurrenceIncidence MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (σ : ∀ f,Equiv.Perm (Fin (D.boundaryCount f)))
variable (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

/-- Puncture scalars and genus are not changed by the re-basing. -/
def reorderPunctures (P : D.Punctures R) : (D.reorderBoundary σ).Punctures R :=
  ⟨P.count,P.scalar⟩

lemma reorder_boundaryEdge_eval (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f (σ f b))) :
    ((D.reorderBoundary σ).boundaryEdgeWord f b i).eval φ (D.reorderGenerators σ g)=
      (D.boundaryEdgeWord f (σ f b) i).eval φ g := by
  apply MatrixIso.unit_injective
  erw [(D.reorderBoundary σ).boundaryEdge_iso,D.boundaryEdge_iso]
  rfl

lemma reorder_boundaryWord_eval (f : F) (b : Fin (D.boundaryCount f)) :
    ((D.reorderBoundary σ).boundaryWord f b).eval φ (D.reorderGenerators σ g)=
      (D.boundaryWord f (σ f b)).eval φ g := by
  erw [(D.reorderBoundary σ).boundaryWord_eval_raw,D.boundaryWord_eval_raw]
  exact congrArg (fun x : Fin (D.boundaryLength f (σ f b)) →
    (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ => (List.ofFn x).reverse.prod)
      (funext fun i => D.reorder_boundaryEdge_eval σ φ g f b i)

lemma reorder_parentWord_eval (s : S) :
    ((D.reorderBoundary σ).parentWord s).eval φ (D.reorderGenerators σ g)=
      (D.parentWord s).eval φ g := by
  apply MatrixIso.unit_injective
  unfold parentWord
  erw [Term.eval_cast_iso φ (D.reorderGenerators σ g) ((D.reorderBoundary σ).seamRank s),
    Term.eval_cast_iso φ g (D.seamRank s)]
  rfl

lemma reorder_seamLeft_eval (s : S) :
    ((D.reorderBoundary σ).seamLeft s).eval φ (D.reorderGenerators σ g)=
      (D.seamLeft s).eval φ g := by
  simp only [seamLeft,Term.eval,D.reorder_parentWord_eval]
  rfl

lemma reorder_seamRight_eval (s : S) :
    ((D.reorderBoundary σ).seamRight s).eval φ (D.reorderGenerators σ g)=
      (D.seamRight s).eval φ g := rfl

lemma reorder_surfaceTarget_eval (P : D.Punctures R) (f : F) :
    ((D.reorderBoundary σ).surfaceTarget (D.reorderPunctures σ P) f).eval φ
      (D.reorderGenerators σ g)=(D.surfaceTarget P f).eval φ g := rfl

lemma reorder_surfaceWord_eval (f : F) :
    ((D.reorderBoundary σ).surfaceWord f).eval φ (D.reorderGenerators σ g)=
      (List.ofFn (fun k => (D.commutatorWord f k).eval φ g)).prod*
      (List.ofFn (fun b => (D.boundaryWord f (σ f b)).eval φ g)).prod := by
  simp only [surfaceWord,Term.eval,wordProduct_eval_raw,List.map_ofFn,Function.comp_def]
  erw [show (fun b : Fin (D.boundaryCount f) =>
      ((D.reorderBoundary σ).boundaryWord f b).eval φ (D.reorderGenerators σ g)) =
    (fun b => (D.boundaryWord f (σ f b)).eval φ g) from
      funext (D.reorder_boundaryWord_eval σ φ g f)]
  rfl

/-- The choices depend only on the finite permutation, not on a solution or on a coefficient field.
They are based path words. -/
def reorderPathWords (f : F) : Fin (D.boundaryCount f) → FreeGroup (Fin (D.boundaryCount f)) :=
  (SurfaceSurgery.Hurwitz.finPresentation (σ f)).paths

lemma reorderPathWords_spec (f : F) {H : Type} [Group H]
    (x : Fin (D.boundaryCount f) → H) :
    (List.ofFn (fun b => (FreeGroup.lift x) (D.reorderPathWords σ f (σ f b))*x (σ f b)*
      ((FreeGroup.lift x) (D.reorderPathWords σ f (σ f b)))⁻¹)).prod=(List.ofFn x).prod :=
  SurfaceSurgery.Hurwitz.finPresentation_spec (σ f) x

/-- Evaluate those same paths over an arbitrary coefficient ring. -/
def reorderCircleBases : D.CircleBases (R:=A) := fun ⟨f,b⟩ =>
  MatrixIso.unit ((FreeGroup.lift (fun c => (D.boundaryWord f c).eval φ g))
    (D.reorderPathWords σ f b))

def basedReorderGenerators := D.reorderGenerators σ
  (D.gaugeGenerators (D.reorderCircleBases σ φ g) g)

lemma basedReorder_surfaceWord (f : F) :
    ((D.reorderBoundary σ).surfaceWord f).eval φ (D.basedReorderGenerators σ φ g)=
      (D.surfaceWord f).eval φ g := by
  rw [basedReorderGenerators,D.reorder_surfaceWord_eval]
  simp only [D.boundaryWord_gauge,reorderCircleBases,MatrixIso.toUnit_unit]
  rw [D.reorderPathWords_spec]
  simp only [surfaceWord,Term.eval,wordProduct_eval_raw,List.map_ofFn]
  rfl

variable [Algebra R A]
/-- Full sewn-diagram solution after arbitrary reordering of boundary circles. -/
def basedReorderSolution (P : D.Punctures R) (x : D.Solution P A) :
    (D.reorderBoundary σ).Solution (D.reorderPunctures σ P) A := by
  let G := D.reorderCircleBases σ (algebraMap R A) x.val.val
  refine ⟨⟨D.basedReorderGenerators σ (algebraMap R A) x.val.val,?_⟩,?_⟩
  · intro j
    cases j with
    | inl f =>
      change SameFramedFlag (fun _ => 0)
        (matrixUnitEquiv (((D.reorderBoundary σ).surfaceWord f).eval (algebraMap R A)
          (D.basedReorderGenerators σ (algebraMap R A) x.val.val)))
        (matrixUnitEquiv (((D.reorderBoundary σ).surfaceTarget (D.reorderPunctures σ P) f).eval
          (algebraMap R A) (D.basedReorderGenerators σ (algebraMap R A) x.val.val)))
      rw [D.basedReorder_surfaceWord]
      exact x.val.property (.inl f)
    | inr s =>
      change SameFramedFlag (D.seamGrade s)
        (matrixUnitEquiv (((D.reorderBoundary σ).seamLeft s).eval (algebraMap R A)
          (D.reorderGenerators σ (D.gaugeGenerators G x.val.val))))
        (matrixUnitEquiv (((D.reorderBoundary σ).seamRight s).eval (algebraMap R A)
          (D.reorderGenerators σ (D.gaugeGenerators G x.val.val))))
      rw [D.reorder_seamLeft_eval,D.reorder_seamRight_eval]
      exact D.seamHolds_gauge (algebraMap R A) G x.val.val s (x.val.property (.inr s))
  · intro v
    change ((D.reorderBoundary σ).vertexComparison
      (D.reorderGenerators σ (D.gaugeGenerators G x.val.val)) v).Holds
    rw [D.reorder_vertexComparison]
    exact D.vertexHolds_gauge G x.val.val x.property v
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
