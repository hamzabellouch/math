import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.GeneratorGauge

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
variable (D : Diagram F S V arity)

/-- The unique outgoing boundary side at the corner containing a germ. This uses the corner
involution, not the boundary-circle color. -/
def sourceCorner (x : Germ S arity) : Side S arity :=
  if x.2=positive x.1 then D.ports.vertexAssembly.corners.boundaryNext x.1 else x.1

@[simp] lemma sourceCorner_start (a : Side S arity) : D.sourceCorner (start a)=a := by
  simp [sourceCorner,start]
@[simp] lemma sourceCorner_finish (a : Side S arity) :
    D.sourceCorner (finish a)=D.ports.vertexAssembly.corners.boundaryNext a := by
  simp [sourceCorner,finish]

lemma sourceCorner_facet (x : Germ S arity) :
    D.ports.facet (D.sourceCorner x)=D.ports.facet x.1 := by
  unfold sourceCorner
  split
  · exact D.ports.vertexAssembly.corners.boundaryNext_facet _
  · rfl

lemma sourceCorner_mate (x : Germ S arity) :
    D.sourceCorner (D.ports.vertexAssembly.corners.mate x)=D.sourceCorner x := by
  by_cases h : x.2=positive x.1
  · have hx : x=finish x.1 := Prod.ext rfl h
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    simp only [sourceCorner_finish]
    rw [D.ports.vertexAssembly.corners.mate_finish]
    change D.sourceCorner (start (D.ports.vertexAssembly.corners.boundaryNext x.1))=_
    simp only [sourceCorner_start]
  · have hh : x.2= !(positive x.1) := Bool.eq_not_iff.mpr h
    have hx : x=start x.1 := Prod.ext rfl hh
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    simp only [sourceCorner_start]
    rw [D.ports.vertexAssembly.corners.mate_start]
    change D.sourceCorner (finish (D.ports.vertexAssembly.corners.boundaryNext.symm x.1))=_
    rw [sourceCorner_finish,Equiv.apply_symm_apply]

/-- A independent basis at each boundary corner. -/
abbrev CornerBases := (a : Side S arity) →
  MatrixIso R (Fin (D.rank (D.ports.facet a))) (Fin (D.rank (D.ports.facet a)))

def cornerBasis (G : D.CornerBases (R:=R)) (x : Germ S arity) :
    MatrixIso R (Fin (D.rank (D.ports.facet x.1))) (Fin (D.rank (D.ports.facet x.1))) :=
  (G (D.sourceCorner x)).reindex
    (finCongr (congrArg D.rank (D.sourceCorner_facet x)).symm)
    (finCongr (congrArg D.rank (D.sourceCorner_facet x)).symm)

lemma cornerBasis_mate (G : D.CornerBases (R:=R)) (x : Germ S arity) :
    (D.cornerBasis G (D.ports.vertexAssembly.corners.mate x)).reindex
      (finCongr (congrArg D.rank (D.ports.vertexAssembly.corners.sameFacet x)).symm)
      (finCongr (congrArg D.rank (D.ports.vertexAssembly.corners.sameFacet x)).symm)=
      D.cornerBasis G x := by
  exact MatrixIso.finite_basis_transport (fun a : Side S arity => D.rank (D.ports.facet a)) G
    _ _ _ _ _ _ (D.sourceCorner_mate x).symm _

lemma sourceCorner_localMate (x : LocalEnd V D.ports.kind) :
    D.sourceCorner (D.ports.realize (localMate x))=D.sourceCorner (D.ports.realize x) := by
  have h := D.sourceCorner_mate (D.ports.realize x)
  change D.sourceCorner (D.ports.realize (localMate (D.ports.realize.symm
    (D.ports.realize x))))=_ at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Every local vertex gets a coherent basis system without any new compatibility hypothesis. -/
def cornerVertexBases (G : D.CornerBases (R:=R)) (v : V) :
    (D.vertexRanks v).CoherentBases (R:=R) where
  basis p c := D.cornerBasis G (D.ports.realize ⟨v,p,c⟩)
  corner x := by
    exact MatrixIso.finite_basis_transport
      (fun a : Side S arity => D.rank (D.ports.facet a)) G _ _ _ _ _ _
      (D.sourceCorner_localMate ⟨v,x⟩).symm _

end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
variable (D : Diagram F S V arity) (G : D.CornerBases (R:=R))

/-- The endpoint is shared by the whole ordered child list, with its own opposite-oriented boundary
corner for each child. -/
def cornerColumns (s : S) (b : Bool) : MatrixIso R (Fin (D.seamDim s)) (Fin (D.seamDim s)) :=
  (MatrixIso.block (fun j => D.cornerBasis G (⟨s,some j⟩,b))).reindex
    (blockIndex (D.childDim s)) (blockIndex (D.childDim s))

def cornerParent (s : S) (b : Bool) : MatrixIso R (Fin (D.seamDim s)) (Fin (D.seamDim s)) :=
  (D.cornerBasis G (⟨s,none⟩,b)).reindex (finCongr (D.seamRank s).symm)
    (finCongr (D.seamRank s).symm)

lemma cornerColumns_port (p : LocalPort V D.ports.kind) :
    (D.cornerColumns G (D.ports.attach p).1 (D.ports.attach p).2).reindex
      (D.portColumnIndex p) (D.portColumnIndex p)=(D.cornerVertexBases G p.1).columns p.2 := by
  unfold cornerColumns
  erw [MatrixIso.reindex_reindex_eq]
  have ee : (D.portColumnIndex p).trans (blockIndex (D.childDim (D.ports.attach p).1))=
      Equiv.sigmaCongr (D.ports.childEquiv p)
        (fun i => Equiv.refl (Fin (D.childDim (D.ports.attach p).1 (D.ports.childEquiv p i)))) := by
    unfold portColumnIndex
    erw [Equiv.trans_assoc,Equiv.symm_trans_self,Equiv.trans_refl]
    rfl
  erw [ee,MatrixIso.block_reindex_sigma]
  rfl

lemma cornerParent_port (p : LocalPort V D.ports.kind) :
    (D.cornerParent G (D.ports.attach p).1 (D.ports.attach p).2).reindex
      (D.portRowIndex p) (D.portRowIndex p)=(D.cornerVertexBases G p.1).basis p.2 none := by
  unfold cornerParent portRowIndex
  erw [MatrixIso.reindex_reindex_eq]
  have ee : (finCongr (D.seamRank (D.ports.attach p).1)).trans
      (finCongr (D.seamRank (D.ports.attach p).1).symm)=Equiv.refl _ := by ext i; rfl
  erw [ee,MatrixIso.reindex_refl_eq]
  rfl

/-- Path transport transforms from its start corner to its finish; seam frames transform at the
precise endpoint, not per boundary circle. -/
def cornerGaugeGenerators
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ) :
    (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ
  | .side a => (((D.cornerBasis G (start a)).symm.trans (MatrixIso.unit (g (.side a)))).trans
      (D.cornerBasis G (finish a))).toUnit
  | .frame s b => (((D.cornerColumns G s b).symm.trans (MatrixIso.unit (g (.frame s b)))).trans
      (D.cornerParent G s b)).toUnit
  | .handle f k b => g (.handle f k b)

lemma portFrame_cornerGauge
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (v : V) :
    (fun p => D.portFrame (D.cornerGaugeGenerators G g) ⟨v,p⟩)=
      (D.cornerVertexBases G v).reframe (fun p => D.portFrame g ⟨v,p⟩) := by
  funext p
  unfold portFrame
  simp only [cornerGaugeGenerators]
  erw [MatrixIso.unit_toUnit]
  erw [MatrixIso.reindex_trans _ _ (D.portColumnIndex ⟨v,p⟩) (D.portRowIndex ⟨v,p⟩)
    (D.portRowIndex ⟨v,p⟩)]
  erw [MatrixIso.reindex_trans _ _ (D.portColumnIndex ⟨v,p⟩) (D.portColumnIndex ⟨v,p⟩)
    (D.portRowIndex ⟨v,p⟩)]
  erw [← MatrixIso.reindex_symm_eq,D.cornerColumns_port,D.cornerParent_port]
  rfl

theorem vertexHolds_cornerGauge
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (h : D.VertexHolds g) : D.VertexHolds (D.cornerGaugeGenerators G g) := by
  intro v
  unfold vertexComparison
  rw [D.portFrame_cornerGauge]
  exact (D.cornerVertexBases G v).comparison_holds _ (h v)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open HomTransport
open OccurrenceIncidence MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (φ : R →+* A)
variable (G : D.CornerBases (R:=A))
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

lemma parentWord_cornerGauge (s : S) :
    MatrixIso.unit ((D.parentWord s).eval φ (D.cornerGaugeGenerators G g))=
      (((D.cornerParent G s false).symm.trans
        (MatrixIso.unit ((D.parentWord s).eval φ g))).trans (D.cornerParent G s true)) := by
  unfold parentWord
  erw [Term.eval_cast_iso φ (D.cornerGaugeGenerators G g) (D.seamRank s),
    Term.eval_cast_iso φ g (D.seamRank s)]
  simp only [sideWord,Term.eval,cornerGaugeGenerators]
  erw [MatrixIso.unit_toUnit,MatrixIso.bases_reindex]
  rfl

lemma childInverse_cornerGauge (s : S) :
    MatrixIso.unit (blockUnit (D.childDim s)
      (fun j => ((D.childWord s j).eval φ (D.cornerGaugeGenerators G g))⁻¹))=
      (((D.cornerColumns G s false).symm.trans
        (MatrixIso.unit (blockUnit (D.childDim s)
          (fun j => ((D.childWord s j).eval φ g)⁻¹)))).trans (D.cornerColumns G s true)) := by
  let B (b : Bool) (j : Fin (arity s)) :
      MatrixIso A (Fin (D.childDim s j)) (Fin (D.childDim s j)) :=
    D.cornerBasis G (⟨s,some j⟩,b)
  let x (j : Fin (arity s)) : (Matrix (Fin (D.childDim s j)) (Fin (D.childDim s j)) A)ˣ :=
    g (.side ⟨s,some j⟩)
  have hg (j) : (D.childWord s j).eval φ (D.cornerGaugeGenerators G g) =
      (((B true j).symm.trans (MatrixIso.unit (x j))).trans (B false j)).toUnit := rfl
  have hx (j) : (D.childWord s j).eval φ g = x j := rfl
  simp_rw [hg,hx]
  change MatrixIso.unit (blockUnit (D.childDim s) (fun j =>
      ((((B true j).symm.trans (MatrixIso.unit (x j))).trans (B false j)).toUnit)⁻¹)) =
    ((((MatrixIso.block (B false)).reindex (blockIndex (D.childDim s)) (blockIndex (D.childDim s))).symm.trans
      (MatrixIso.unit (blockUnit (D.childDim s) (fun j => (x j)⁻¹)))).trans
      ((MatrixIso.block (B true)).reindex (blockIndex (D.childDim s)) (blockIndex (D.childDim s))))
  rw [MatrixIso.unit_block]
  simp only [MatrixIso.unit_inv,MatrixIso.unit_toUnit,MatrixIso.trans_symm_eq,
    MatrixIso.symm_symm_eq]
  rw [MatrixIso.block_trans,MatrixIso.block_trans,MatrixIso.block_symm]
  rw [MatrixIso.unit_block]
  simp only [MatrixIso.unit_inv,← MatrixIso.trans_assoc]
  erw [← MatrixIso.bases_reindex]

lemma seamLeft_cornerGauge (s : S) :
    MatrixIso.unit ((D.seamLeft s).eval φ (D.cornerGaugeGenerators G g))=
      (((D.cornerColumns G s false).symm.trans
        (MatrixIso.unit ((D.seamLeft s).eval φ g))).trans (D.cornerParent G s true)) := by
  simp only [seamLeft,Term.eval,MatrixIso.unit_mul,frameWord,cornerGaugeGenerators]
  erw [MatrixIso.unit_toUnit,D.parentWord_cornerGauge φ G g]
  exact MatrixIso.bases_trans _ _ _ _ _

lemma seamRight_cornerGauge (s : S) :
    MatrixIso.unit ((D.seamRight s).eval φ (D.cornerGaugeGenerators G g))=
      (((D.cornerColumns G s false).symm.trans
        (MatrixIso.unit ((D.seamRight s).eval φ g))).trans (D.cornerParent G s true)) := by
  simp only [seamRight,Term.eval,frameWord,cornerGaugeGenerators]
  erw [MatrixIso.unit_mul,MatrixIso.unit_mul,MatrixIso.unit_toUnit,D.childInverse_cornerGauge φ G g]
  exact MatrixIso.bases_trans _ _ _ _ _

lemma cornerColumns_grade (s : S) (b : Bool) :
    MatrixIso.GradeDiagonal (D.seamGrade s) (D.cornerColumns G s b).val ∧
    MatrixIso.GradeDiagonal (D.seamGrade s) (D.cornerColumns G s b).inv := by
  have h := MatrixIso.block_GradeDiagonal (fun j : Fin (arity s) => j.val)
    (fun j => D.cornerBasis G (⟨s,some j⟩,b))
  exact ⟨MatrixIso.GradeDiagonal_reindex _ _ h.1 _,
    MatrixIso.GradeDiagonal_reindex _ _ h.2 _⟩

/-- Every regular seam equation is preserved, with the full graded identifications and opposite
child orientations. -/
theorem seamHolds_cornerGauge (s : S)
    (h : SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g))) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ (D.cornerGaugeGenerators G g)))
      (matrixUnitEquiv ((D.seamRight s).eval φ (D.cornerGaugeGenerators G g))) := by
  simp only [← MatrixIso.unit_linearEquiv] at h ⊢
  rw [D.seamLeft_cornerGauge,D.seamRight_cornerGauge]
  have hg := D.cornerColumns_grade G s false
  exact MatrixIso.sameFramedFlag_bases _ _ _ (D.cornerColumns G s false).symm
    (D.cornerParent G s true) hg.2 hg.1 h
end IntegralCharacterVarieties.SurfacePresentation.Diagram

/- Based boundary reorderings are Hurwitz operations, never an unbased permutation of noncommuting
holonomies. -/

end

end OAI
