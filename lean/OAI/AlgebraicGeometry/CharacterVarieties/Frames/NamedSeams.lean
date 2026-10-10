import OAI.AlgebraicGeometry.CharacterVarieties.Frames.BandBases
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.GeneratorGauge

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R α β α' β' : Type*} [CommRing R] [Fintype α] [Fintype β]
  [Fintype α'] [Fintype β']
lemma sameFramedFlag_reindex (a : α → ℕ) (x y : MatrixIso R α β)
    (e : α' ≃ α) (f : β' ≃ β)
    (h : SameFramedFlag a x.linearEquiv y.linearEquiv) :
    SameFramedFlag (fun i => a (e i)) (x.reindex e f).linearEquiv (y.reindex e f).linearEquiv := by
  rw [sameFramedFlag_iff] at h ⊢
  intro i j hij
  change (y.inv.submatrix e f * x.val.submatrix f e) i j = _
  rw [Matrix.submatrix_mul_equiv]
  change (y.inv*x.val) (e i) (e j)=_
  rw [h (e i) (e j) hij]
  exact congrFun (congrFun (Matrix.submatrix_one_equiv e) i) j
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)

def namedParentLinear := (MatrixIso.unit (g (.side ⟨q,none⟩))).linearEquiv
def namedChildInverse := (MatrixIso.block (fun i : Fin (arity q) =>
  (MatrixIso.unit (g (.side ⟨q,some i⟩))⁻¹))).linearEquiv

lemma namedSeamLeft (φ : R →+* K) : D.namedSeamFrame q ((D.seamLeft q).eval φ g)=
    (D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g) := by
  unfold namedSeamFrame namedParentLinear
  simp only [seamLeft,Term.eval,frameWord]
  erw [MatrixIso.unit_mul]
  erw [MatrixIso.reindex_trans _ _ (blockIndex (D.childDim q)).symm
    (finCongr (D.seamRank q)) (finCongr (D.seamRank q))]
  have he : (MatrixIso.unit ((D.parentWord q).eval φ g)).reindex
      (finCongr (D.seamRank q)) (finCongr (D.seamRank q))=
      MatrixIso.unit (g (.side ⟨q,none⟩)) := by
    unfold parentWord
    erw [Term.eval_cast_iso φ g (D.seamRank q)]
    simp only [sideWord,Term.eval]
    erw [MatrixIso.reindex_reindex_eq]
    have e : (finCongr (D.seamRank q)).trans (finCongr (D.seamRank q).symm)=Equiv.refl _ := by ext i; rfl
    erw [e,MatrixIso.reindex_refl_eq]
    rfl
  erw [he]
  ext x i
  exact congrFun (MatrixIso.linearEquiv_trans_apply _ _ x) i

lemma namedSeamRight (φ : R →+* K) : D.namedSeamFrame q ((D.seamRight q).eval φ g)=
    (D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true))) := by
  unfold namedSeamFrame namedChildInverse
  simp only [seamRight,Term.eval,frameWord,childWord,sideWord]
  erw [MatrixIso.unit_mul,MatrixIso.unit_block]
  erw [MatrixIso.reindex_trans _ _ (blockIndex (D.childDim q)).symm
    (blockIndex (D.childDim q)).symm (finCongr (D.seamRank q))]
  simp only [MatrixIso.reindex_reindex_eq]
  have ee := Equiv.symm_trans_self (blockIndex (D.childDim q))
  erw [ee,MatrixIso.reindex_refl_eq]
  apply LinearEquiv.ext
  intro x
  exact MatrixIso.linearEquiv_trans_apply _ _ x

/-- The named seam relation of a solution. -/
lemma old_named_seam [Algebra R K] (P : D.Punctures R) (x : D.Solution P K) :
    SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
      ((D.namedSeamFrame q (x.val.val (.frame q false))).trans (D.namedParentLinear q x.val.val))
      ((D.namedChildInverse q x.val.val).trans (D.namedSeamFrame q (x.val.val (.frame q true)))) := by
  have h := x.val.property (.inr q)
  change SameFramedFlag (D.seamGrade q)
    (matrixUnitEquiv ((D.seamLeft q).eval (algebraMap R K) x.val.val))
    (matrixUnitEquiv ((D.seamRight q).eval (algebraMap R K) x.val.val)) at h
  simp only [← MatrixIso.unit_linearEquiv] at h
  have z := MatrixIso.sameFramedFlag_reindex (D.seamGrade q) _ _
    (blockIndex (D.childDim q)).symm (finCongr (D.seamRank q)) h
  have he : (fun i => D.seamGrade q ((blockIndex (D.childDim q)).symm i))=
      (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val) := by
    funext i
    simp only [seamGrade,Equiv.apply_symm_apply]
  erw [he] at z
  change SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
    (D.namedSeamFrame q ((D.seamLeft q).eval (algebraMap R K) x.val.val))
    (D.namedSeamFrame q ((D.seamRight q).eval (algebraMap R K) x.val.val)) at z
  erw [D.namedSeamLeft,D.namedSeamRight] at z
  exact z
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R α β α' β' : Type*} [CommRing R] [Fintype α] [Fintype β]
  [Fintype α'] [Fintype β']
lemma sameFramedFlag_reindex_iff (a : α → ℕ) (x y : MatrixIso R α β)
    (e : α' ≃ α) (f : β' ≃ β) :
    SameFramedFlag (fun i => a (e i)) (x.reindex e f).linearEquiv
      (y.reindex e f).linearEquiv ↔ SameFramedFlag a x.linearEquiv y.linearEquiv := by
  constructor
  · intro h
    rw [sameFramedFlag_iff] at h ⊢
    intro i j hij
    have hh := h (e.symm i) (e.symm j) (by simpa only [Equiv.apply_symm_apply] using hij)
    change (y.inv.submatrix e f * x.val.submatrix f e) (e.symm i) (e.symm j)=_ at hh
    rw [Matrix.submatrix_mul_equiv] at hh
    simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,
      Matrix.one_apply,Equiv.symm_apply_eq,Equiv.apply_symm_apply] using hh
  · exact sameFramedFlag_reindex a x y e f
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S)
    (φ : R →+* K)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
lemma named_seam_iff :
    SameFramedFlag (D.seamGrade q)
      (matrixUnitEquiv ((D.seamLeft q).eval φ g))
      (matrixUnitEquiv ((D.seamRight q).eval φ g)) ↔
    SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
      ((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g))
      ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true)))) := by
  have z := MatrixIso.sameFramedFlag_reindex_iff (D.seamGrade q)
    (MatrixIso.unit ((D.seamLeft q).eval φ g)) (MatrixIso.unit ((D.seamRight q).eval φ g))
    (blockIndex (D.childDim q)).symm (finCongr (D.seamRank q))
  have he : (fun i => D.seamGrade q ((blockIndex (D.childDim q)).symm i))=
      (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val) := by
    funext i
    simp only [seamGrade,Equiv.apply_symm_apply]
  erw [he] at z
  change SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
    (D.namedSeamFrame q ((D.seamLeft q).eval φ g))
    (D.namedSeamFrame q ((D.seamRight q).eval φ g)) ↔ _ at z
  erw [D.namedSeamLeft,D.namedSeamRight] at z
  exact z.symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
