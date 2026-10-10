import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.ReorderedSolutions

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {A : Type*} [CommRing A]
variable {α β : Type*} [Fintype α] [Fintype β]
lemma bases_symm_cancel (C : MatrixIso A α α) (P : MatrixIso A β β) (x : MatrixIso A α β) :
    (C.trans ((C.symm.trans x).trans P)).trans P.symm=x := by
  simp only [trans_assoc,trans_symm_self,trans_refl,
    ← trans_assoc C C.symm,refl_trans]
end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity)
variable (G : D.CircleBases (R:=A))
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

@[simp] lemma sideBasis_symm (a : Side S arity) :
    D.sideBasis (fun B => (G B).symm) a=(D.sideBasis G a).symm := rfl
@[simp] lemma seamParentBasis_symm (s : S) :
    D.seamParentBasis (fun B => (G B).symm) s=(D.seamParentBasis G s).symm := rfl
@[simp] lemma seamColumnsBasis_symm (s : S) :
    D.seamColumnsBasis (fun B => (G B).symm) s=(D.seamColumnsBasis G s).symm := rfl

/-- The coordinate gauge has a two-sided inverse on all old named side, frame and handle
coordinates. Seams/vertices are never forgotten. -/
theorem gaugeGenerators_inverse :
    D.gaugeGenerators (fun B => (G B).symm) (D.gaugeGenerators G g)=g := by
  funext e
  cases e with
  | side a =>
    apply MatrixIso.unit_injective
    simp only [gaugeGenerators]
    erw [MatrixIso.unit_toUnit,MatrixIso.unit_toUnit]
    rw [D.sideBasis_symm,MatrixIso.symm_symm_eq]
    exact MatrixIso.bases_symm_cancel _ _ _
  | frame s b =>
    apply MatrixIso.unit_injective
    simp only [gaugeGenerators]
    erw [MatrixIso.unit_toUnit,MatrixIso.unit_toUnit]
    rw [D.seamColumnsBasis_symm,D.seamParentBasis_symm,MatrixIso.symm_symm_eq]
    exact MatrixIso.bases_symm_cancel _ _ _
  | handle f k b => rfl

/-- A generator-coordinate equivalence, meaningful over the full ring. -/
def gaugeEquiv : ((e : D.Generator) →
      (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ) ≃
    ((e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ) where
  toFun := D.gaugeGenerators G
  invFun := D.gaugeGenerators (fun B => (G B).symm)
  left_inv := D.gaugeGenerators_inverse G
  right_inv x := by
    simpa only [MatrixIso.symm_symm_eq] using D.gaugeGenerators_inverse (fun B => (G B).symm) x
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (G : D.CornerBases (R:=A))

@[simp] lemma cornerBasis_symm (a : Germ S arity) :
    D.cornerBasis (fun B => (G B).symm) a=(D.cornerBasis G a).symm := rfl
@[simp] lemma cornerParent_symm (s : S) (b : Bool) :
    D.cornerParent (fun B => (G B).symm) s b=(D.cornerParent G s b).symm := rfl
@[simp] lemma cornerColumns_symm (s : S) (b : Bool) :
    D.cornerColumns (fun B => (G B).symm) s b=(D.cornerColumns G s b).symm := rfl

lemma cornerGaugeGenerators_inverse
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ) :
    D.cornerGaugeGenerators (fun B => (G B).symm) (D.cornerGaugeGenerators G g)=g := by
  funext e
  cases e with
  | side a =>
    apply MatrixIso.unit_injective
    simp only [cornerGaugeGenerators]
    erw [MatrixIso.unit_toUnit,MatrixIso.unit_toUnit]
    rw [D.cornerBasis_symm,D.cornerBasis_symm,MatrixIso.symm_symm_eq]
    exact MatrixIso.bases_symm_cancel _ _ _
  | frame s b =>
    apply MatrixIso.unit_injective
    simp only [cornerGaugeGenerators]
    erw [MatrixIso.unit_toUnit,MatrixIso.unit_toUnit]
    rw [D.cornerColumns_symm,D.cornerParent_symm,MatrixIso.symm_symm_eq]
    exact MatrixIso.bases_symm_cancel _ _ _
  | handle f k b => rfl

lemma basedCorner_inverse (hG : CornerBases.Based D G) :
    CornerBases.Based D (fun B => (G B).symm) := by
  intro f b
  change (D.boundaryCornerBasis G f b ⟨0,D.boundaryPositive f b⟩).symm=MatrixIso.refl
  rw [hG]
  rfl

variable {R : Type} [CommRing R] [Algebra R A]
/-- Full-ring bijective change of every corner frame in the solution. No vertex, quotient
identification or surface equation is lost. -/
def basedCornerEquiv (hG : CornerBases.Based D G) (P : D.Punctures R) :
    D.Solution P A ≃ D.Solution P A where
  toFun := D.basedCornerSolution G hG P
  invFun := D.basedCornerSolution (fun B => (G B).symm) (D.basedCorner_inverse G hG) P
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact D.cornerGaugeGenerators_inverse G x.val.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change D.cornerGaugeGenerators G (D.cornerGaugeGenerators (fun B => (G B).symm) x.val.val)=x.val.val
    simpa only [MatrixIso.symm_symm_eq] using
      D.cornerGaugeGenerators_inverse (fun B => (G B).symm) x.val.val
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
