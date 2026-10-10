import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.VertexGauge

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {α : Type*} [Fintype α]

def toUnit [DecidableEq α] (x : MatrixIso R α α) : (Matrix α α R)ˣ where
  val := x.val
  inv := x.inv
  val_inv := by
    ext i j
    by_cases h : i=j <;> simpa [Matrix.one_apply,h] using congrFun (congrFun x.val_inv i) j
  inv_val := by
    ext i j
    by_cases h : i=j <;> simpa [Matrix.one_apply,h] using congrFun (congrFun x.inv_val i) j

variable [DecidableEq α]

@[simp] lemma unit_toUnit (x : MatrixIso R α α) : unit x.toUnit=x := by
  apply ext <;> rfl
@[simp] lemma toUnit_unit (x : (Matrix α α R)ˣ) : (unit x).toUnit=x := by
  apply Units.ext; rfl
@[simp] lemma unit_mul (x y : (Matrix α α R)ˣ) : unit (x*y)=(unit y).trans (unit x) := by
  apply ext <;> rfl
@[simp] lemma unit_inv (x : (Matrix α α R)ˣ) : unit x⁻¹=(unit x).symm := by
  apply ext <;> rfl
end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
variable {R : Type*} [CommRing R]

/-- The whole ordered child fiber, retaining every old occurrence. -/
def seamColumnsBasis (G : D.CircleBases (R:=R)) (s : S) :
    MatrixIso R (Fin (D.seamDim s)) (Fin (D.seamDim s)) :=
  (MatrixIso.block (fun j => D.sideBasis G ⟨s,some j⟩)).reindex
    (blockIndex (D.childDim s)) (blockIndex (D.childDim s))

def seamParentBasis (G : D.CircleBases (R:=R)) (s : S) :
    MatrixIso R (Fin (D.seamDim s)) (Fin (D.seamDim s)) :=
  (D.sideBasis G ⟨s,none⟩).reindex (finCongr (D.seamRank s).symm)
    (finCongr (D.seamRank s).symm)

lemma port_columns_basis (G : D.CircleBases (R:=R)) (p : LocalPort V D.ports.kind) :
    (D.seamColumnsBasis G (D.ports.attach p).1).reindex
      (D.portColumnIndex p) (D.portColumnIndex p)=(D.vertexBases G p.1).columns p.2 := by
  unfold seamColumnsBasis
  erw [MatrixIso.reindex_reindex_eq]
  have ee : (D.portColumnIndex p).trans (blockIndex (D.childDim (D.ports.attach p).1))=
      Equiv.sigmaCongr (D.ports.childEquiv p)
        (fun i => Equiv.refl (Fin (D.childDim (D.ports.attach p).1 (D.ports.childEquiv p i)))) := by
    unfold portColumnIndex
    erw [Equiv.trans_assoc,Equiv.symm_trans_self,Equiv.trans_refl]
    rfl
  erw [ee,MatrixIso.block_reindex_sigma]
  rfl

lemma port_parent_basis (G : D.CircleBases (R:=R)) (p : LocalPort V D.ports.kind) :
    (D.seamParentBasis G (D.ports.attach p).1).reindex
      (D.portRowIndex p) (D.portRowIndex p)=(D.vertexBases G p.1).basis p.2 none := by
  unfold seamParentBasis portRowIndex
  erw [MatrixIso.reindex_reindex_eq]
  have ee : (finCongr (D.seamRank (D.ports.attach p).1)).trans
      (finCongr (D.seamRank (D.ports.attach p).1).symm)=Equiv.refl _ := by ext i; rfl
  erw [ee,MatrixIso.reindex_refl_eq]
  rfl

/-- These are the old generator coordinates in new boundary base frames: all side occurrences and
BOTH seam ends change together. -/
def gaugeGenerators (G : D.CircleBases (R:=R))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ) :
    (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ
  | .side a => (((D.sideBasis G a).symm.trans (MatrixIso.unit (g (.side a)))).trans
      (D.sideBasis G a)).toUnit
  | .frame s b => (((D.seamColumnsBasis G s).symm.trans (MatrixIso.unit (g (.frame s b)))).trans
      (D.seamParentBasis G s)).toUnit
  | .handle f k b => g (.handle f k b)

lemma portFrame_gauge (G : D.CircleBases (R:=R))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (v : V) :
    (fun p => D.portFrame (D.gaugeGenerators G g) ⟨v,p⟩)=
      (D.vertexBases G v).reframe (fun p => D.portFrame g ⟨v,p⟩) := by
  funext p
  unfold portFrame
  simp only [gaugeGenerators]
  erw [MatrixIso.unit_toUnit]
  erw [MatrixIso.reindex_trans _ _ (D.portColumnIndex ⟨v,p⟩) (D.portRowIndex ⟨v,p⟩)
    (D.portRowIndex ⟨v,p⟩)]
  erw [MatrixIso.reindex_trans _ _ (D.portColumnIndex ⟨v,p⟩) (D.portColumnIndex ⟨v,p⟩)
    (D.portRowIndex ⟨v,p⟩)]
  erw [← MatrixIso.reindex_symm_eq,D.port_columns_basis,D.port_parent_basis]
  rfl

theorem vertexHolds_gauge (G : D.CircleBases (R:=R))
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) R)ˣ)
    (h : D.VertexHolds g) : D.VertexHolds (D.gaugeGenerators G g) := by
  intro v
  unfold vertexComparison
  rw [D.portFrame_gauge]
  exact (D.vertexBases G v).comparison_holds _ (h v)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
open HomTransport
variable {R : Type*} [CommRing R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[simp] theorem symm_symm_eq (x : MatrixIso R α β) : x.symm.symm=x := rfl
@[simp] theorem trans_symm_eq (x : MatrixIso R α β) (y : MatrixIso R β γ) :
    (x.trans y).symm=y.symm.trans x.symm := rfl

lemma block_trans {I : Type*} [Fintype I] {a b c : I → Type*}
    [∀ i,Fintype (a i)] [∀ i,Fintype (b i)] [∀ i,Fintype (c i)]
    (x : ∀ i,MatrixIso R (a i) (b i)) (y : ∀ i,MatrixIso R (b i) (c i)) :
    block (fun i => (x i).trans (y i))=(block x).trans (block y) := by
  apply ext <;> simp only [block,trans,Matrix.blockDiagonal'_mul]

@[simp] lemma block_symm {I : Type*} [Fintype I] {a b : I → Type*}
    [∀ i,Fintype (a i)] [∀ i,Fintype (b i)]
    (x : ∀ i,MatrixIso R (a i) (b i)) : block (fun i => (x i).symm)=(block x).symm := rfl

lemma bases_trans (A : MatrixIso R α α) (B : MatrixIso R β β)
    (C : MatrixIso R γ γ) (x : MatrixIso R α β) (y : MatrixIso R β γ) :
    ((A.symm.trans x).trans B).trans ((B.symm.trans y).trans C)=
      (A.symm.trans (x.trans y)).trans C := by
  simp only [trans_assoc,← trans_assoc B B.symm,trans_symm_self,refl_trans]

@[simp] lemma unit_block {m : ℕ} (d : Fin m → ℕ)
    (x : (j : Fin m) → (Matrix (Fin (d j)) (Fin (d j)) R)ˣ) :
    unit (MatrixExpression.blockUnit d x)=
      (block (fun j => unit (x j))).reindex (MatrixExpression.blockIndex d)
        (MatrixExpression.blockIndex d) := by
  apply ext <;> ext i j <;> simp [unit,block,reindex,MatrixExpression.blockUnit,Matrix.blockDiagonal']

lemma unit_linearEquiv {n : ℕ} (x : (Matrix (Fin n) (Fin n) R)ˣ) :
    (unit x).linearEquiv=matrixUnitEquiv x := by
  apply LinearEquiv.ext
  intro v
  rfl
end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.MatrixExpression
open scoped Classical Matrix
open HomTransport
variable {R A E : Type*} [CommRing R] [CommRing A] {r : E → ℕ}
lemma Term.eval_cast_iso (φ : R →+* A)
    (g : (e : E) → (Matrix (Fin (r e)) (Fin (r e)) A)ˣ)
    {n m : ℕ} (h : n=m) (t : Term R E r n) :
    MatrixIso.unit ((cast (congrArg (Term R E r) h) t).eval φ g)=
      (MatrixIso.unit (t.eval φ g)).reindex (finCongr h.symm) (finCongr h.symm) := by
  subst m
  simp only [cast_eq,finCongr_refl,MatrixIso.reindex_refl_eq]
end IntegralCharacterVarieties.MatrixExpression

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open HomTransport
open OccurrenceIncidence MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (φ : R →+* A)
variable (G : D.CircleBases (R:=A))
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

lemma parentWord_gauge (s : S) :
    MatrixIso.unit ((D.parentWord s).eval φ (D.gaugeGenerators G g))=
      (((D.seamParentBasis G s).symm.trans
        (MatrixIso.unit ((D.parentWord s).eval φ g))).trans (D.seamParentBasis G s)) := by
  unfold parentWord
  erw [Term.eval_cast_iso φ (D.gaugeGenerators G g) (D.seamRank s),
    Term.eval_cast_iso φ g (D.seamRank s)]
  simp only [sideWord,Term.eval,gaugeGenerators]
  erw [MatrixIso.unit_toUnit,MatrixIso.bases_reindex]
  rfl

lemma childInverse_gauge (s : S) :
    MatrixIso.unit (blockUnit (D.childDim s)
      (fun j => ((D.childWord s j).eval φ (D.gaugeGenerators G g))⁻¹))=
      (((D.seamColumnsBasis G s).symm.trans
        (MatrixIso.unit (blockUnit (D.childDim s)
          (fun j => ((D.childWord s j).eval φ g)⁻¹)))).trans (D.seamColumnsBasis G s)) := by
  let B (j : Fin (arity s)) : MatrixIso A (Fin (D.childDim s j)) (Fin (D.childDim s j)) :=
    D.sideBasis G ⟨s,some j⟩
  let x (j : Fin (arity s)) : (Matrix (Fin (D.childDim s j)) (Fin (D.childDim s j)) A)ˣ :=
    g (.side ⟨s,some j⟩)
  have hg (j) : (D.childWord s j).eval φ (D.gaugeGenerators G g) =
      (((B j).symm.trans (MatrixIso.unit (x j))).trans (B j)).toUnit := rfl
  have hx (j) : (D.childWord s j).eval φ g = x j := rfl
  simp_rw [hg,hx]
  change MatrixIso.unit (blockUnit (D.childDim s) (fun j =>
      ((((B j).symm.trans (MatrixIso.unit (x j))).trans (B j)).toUnit)⁻¹)) =
    ((((MatrixIso.block B).reindex (blockIndex (D.childDim s)) (blockIndex (D.childDim s))).symm.trans
      (MatrixIso.unit (blockUnit (D.childDim s) (fun j => (x j)⁻¹)))).trans
      ((MatrixIso.block B).reindex (blockIndex (D.childDim s)) (blockIndex (D.childDim s))))
  rw [MatrixIso.unit_block]
  simp only [MatrixIso.unit_inv,MatrixIso.unit_toUnit,MatrixIso.trans_symm_eq,
    MatrixIso.symm_symm_eq]
  rw [MatrixIso.block_trans,MatrixIso.block_trans,MatrixIso.block_symm]
  rw [MatrixIso.unit_block]
  simp only [MatrixIso.unit_inv,← MatrixIso.trans_assoc]
  erw [← MatrixIso.bases_reindex]

lemma seamLeft_gauge (s : S) :
    MatrixIso.unit ((D.seamLeft s).eval φ (D.gaugeGenerators G g))=
      (((D.seamColumnsBasis G s).symm.trans
        (MatrixIso.unit ((D.seamLeft s).eval φ g))).trans (D.seamParentBasis G s)) := by
  simp only [seamLeft,Term.eval,MatrixIso.unit_mul,frameWord,gaugeGenerators]
  erw [MatrixIso.unit_toUnit,D.parentWord_gauge φ G g]
  exact MatrixIso.bases_trans _ _ _ _ _

lemma seamRight_gauge (s : S) :
    MatrixIso.unit ((D.seamRight s).eval φ (D.gaugeGenerators G g))=
      (((D.seamColumnsBasis G s).symm.trans
        (MatrixIso.unit ((D.seamRight s).eval φ g))).trans (D.seamParentBasis G s)) := by
  simp only [seamRight,Term.eval,frameWord,gaugeGenerators]
  erw [MatrixIso.unit_mul,MatrixIso.unit_mul,MatrixIso.unit_toUnit,D.childInverse_gauge φ G g]
  exact MatrixIso.bases_trans _ _ _ _ _

lemma seamColumns_grade (s : S) :
    MatrixIso.GradeDiagonal (D.seamGrade s) (D.seamColumnsBasis G s).val ∧
    MatrixIso.GradeDiagonal (D.seamGrade s) (D.seamColumnsBasis G s).inv := by
  have h := MatrixIso.block_GradeDiagonal (fun j : Fin (arity s) => j.val)
    (fun j => D.sideBasis G ⟨s,some j⟩)
  exact ⟨MatrixIso.GradeDiagonal_reindex _ _ h.1 _,
    MatrixIso.GradeDiagonal_reindex _ _ h.2 _⟩

/-- Every regular seam equation is preserved, with the full graded identifications and opposite
child orientations. -/
theorem seamHolds_gauge (s : S)
    (h : SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g))) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ (D.gaugeGenerators G g)))
      (matrixUnitEquiv ((D.seamRight s).eval φ (D.gaugeGenerators G g))) := by
  simp only [← MatrixIso.unit_linearEquiv] at h ⊢
  rw [D.seamLeft_gauge,D.seamRight_gauge]
  have hg := D.seamColumns_grade G s
  exact MatrixIso.sameFramedFlag_bases _ _ _ (D.seamColumnsBasis G s).symm
    (D.seamParentBasis G s) hg.2 hg.1 h
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
