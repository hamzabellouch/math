import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BandCutTopology
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.GeneratorGauge

namespace OAI

/-!
# Generator coordinates for a nonseparating cut

The cut sides and endpoint frames determine the new generator coordinates.
Their seam and vertex equations follow from the full-block refinement identities.
-/

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)

lemma bandCutIdentityRank : (D.bandCutDiagram q).seamDim (.inr ())=D.seamDim q := by
  change (∑ _ : Fin 1,D.rank (D.bandCutParent q))=D.seamDim q
  rw [Fin.sum_univ_one]
  exact D.seamRank q

/-- The coordinate equivalence for the singleton child of the identity seam. -/
def bandCutIdentityColumns : Fin ((D.bandCutDiagram q).seamDim (.inr ())) ≃ Fin (D.seamDim q) :=
  (blockIndex ((D.bandCutDiagram q).childDim (.inr ()))).trans
    ((Equiv.uniqueSigma (fun _ : Fin 1 => Fin (D.rank (D.bandCutParent q)))).trans
      (finCongr (D.seamRank q)))

abbrev BandCutUnit := (Matrix (Fin (D.seamDim q)) (Fin (D.seamDim q)) A)ˣ

variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)

/-- The old positive parent-side matrix, in the simultaneous child basis. -/
def bandCutP : D.BandCutUnit (A:=A) q := rebaseUnit (D.seamRank q) (g (.side ⟨q,none⟩))

def bandCutF (b : Bool) : D.BandCutUnit (A:=A) q := g (.frame q b)

/-- Transports on the cut sides, retaining the old child transports. -/
def bandCutSideValues : (a : Side (BandCutSeam S) (bandCutArity arity)) →
    (Matrix (Fin (D.rank ((D.ports.bandCutPorts q).facet a)))
      (Fin (D.rank ((D.ports.bandCutPorts q).facet a))) A)ˣ
  | ⟨.inl (s,k),none⟩ =>
      if hs : s=q then by
        subst s
        exact if k=1 then rebaseUnit (D.seamRank q).symm
          (T⁻¹*J⁻¹*D.bandCutP q g*T) else 1
      else if k=2 then g (.side ⟨s,none⟩) else 1
  | ⟨.inl (s,k),some i⟩ => if k=2 then g (.side ⟨s,some i⟩) else 1
  | ⟨.inr (),none⟩ => 1
  | ⟨.inr (),some _⟩ => rebaseUnit (D.seamRank q).symm J

/-- Endpoint frames realizing both new splits as refinements of the old flags. -/
def bandCutFrameValues : (s : BandCutSeam S) → Bool →
    (Matrix (Fin ((D.bandCutDiagram q).seamDim s))
      (Fin ((D.bandCutDiagram q).seamDim s)) A)ˣ
  | .inl (s,k),e =>
      if hs : s=q then by
        subst s
        exact if k=0 then g (.frame q false)
          else if k=1 then
            if e then T⁻¹*J⁻¹*D.bandCutP q g*D.bandCutF q g false
              else T⁻¹*D.bandCutF q g false
          else if e then g (.frame q true) else D.bandCutP q g*D.bandCutF q g false
      else if k=2 ∧ e=true then g (.frame s true) else g (.frame s false)
  | .inr (),e => ((MatrixIso.unit (if e then T⁻¹ else T⁻¹*J⁻¹)).reindex
      (D.bandCutIdentityColumns q) (finCongr (D.bandCutIdentityRank q))).toUnit

def bandCutPunctures {R : Type} [CommRing R] (P : D.Punctures R) :
    (D.bandCutDiagram q).Punctures R where
  count := P.count
  scalar := P.scalar


def bandCutValues
    (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ) :
    (e : (D.bandCutDiagram q).Generator) →
      (Matrix (Fin ((D.bandCutDiagram q).generatorRank e))
        (Fin ((D.bandCutDiagram q).generatorRank e)) A)ˣ
  | .side a => D.bandCutSideValues q g J T a
  | .frame s e => D.bandCutFrameValues q g J T s e
  | .handle f k b => h f k b
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
variable {A : Type} [CommRing A]

@[simp] lemma rebaseUnit_refl {n : ℕ} (h : n=n) (x : (Matrix (Fin n) (Fin n) A)ˣ) :
    rebaseUnit h x=x := rfl
lemma rebaseUnit_trans {l m n : ℕ} (h : l=m) (k : m=n)
    (x : (Matrix (Fin l) (Fin l) A)ˣ) :
    rebaseUnit k (rebaseUnit h x)=rebaseUnit (h.trans k) x := by subst n; subst m; rfl

lemma rebaseUnit_iso {m n : ℕ} (h : m=n) (x : (Matrix (Fin m) (Fin m) A)ˣ) :
    MatrixIso.unit (rebaseUnit h x)=
      (MatrixIso.unit x).reindex (finCongr h.symm) (finCongr h.symm) := by subst n; rfl

end IntegralCharacterVarieties.SurfacePresentation.Diagram
namespace IntegralCharacterVarieties.MatrixExpression
open scoped Classical Matrix
open SurfacePresentation.Diagram
variable {R A E : Type} [CommRing R] [CommRing A] {rank : E → ℕ}

lemma Term.eval_cast_unit (φ : R →+* A)
    (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) A)ˣ)
    {n m : ℕ} (h : n=m) (t : Term R E rank n) :
    (cast (congrArg (Term R E rank) h) t).eval φ g = rebaseUnit h (t.eval φ g) := by
  subst m; rfl

lemma blockUnit_one {k : ℕ} (d : Fin k → ℕ) :
    blockUnit (R:=A) d (fun _ => 1)=1 := by
  apply Units.ext
  change (Matrix.blockDiagonal' (1 : (j : Fin k) → Matrix (Fin (d j)) (Fin (d j)) A)).submatrix
    (blockIndex d) (blockIndex d)=1
  rw [Matrix.blockDiagonal'_one]
  exact Matrix.submatrix_one_equiv _

lemma uniqueSigma_const_apply {ι α : Type*} [Unique ι] (x : (_i : ι) × α) :
    Equiv.uniqueSigma (fun _ : ι => α) x=x.2 := by
  obtain ⟨i,x⟩ := x
  have hi : i=default := Subsingleton.elim _ _
  subst i
  rfl

/-- A one-child seam retains its specified block ordering. -/
lemma blockUnit_single {n : ℕ} (x : (Matrix (Fin n) (Fin n) A)ˣ) :
    MatrixIso.unit (blockUnit (fun _ : Fin 1 => n) (fun _ => x))=
      (MatrixIso.unit x).reindex
        ((blockIndex (fun _ : Fin 1 => n)).trans (Equiv.uniqueSigma (fun _ => Fin n)))
        ((blockIndex (fun _ : Fin 1 => n)).trans (Equiv.uniqueSigma (fun _ => Fin n))) := by
  apply MatrixIso.ext <;> ext i j
  all_goals
    simp only [MatrixIso.unit,blockUnit,MatrixIso.reindex,Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply,Equiv.trans_apply,uniqueSigma_const_apply]
    rw [dite_eq_left (Subsingleton.elim _ _)]
    simp only [cast_eq] <;> rfl
end IntegralCharacterVarieties.MatrixExpression

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

lemma bandCut_parent_inl (s : S) (k : Fin 3) :
    ((D.bandCutDiagram q).parentWord (.inl (s,k))).eval φ (D.bandCutValues q g J T h)=
      rebaseUnit (D.seamRank s) (D.bandCutSideValues q g J T ⟨.inl (s,k),none⟩) := by
  unfold parentWord
  exact Term.eval_cast_unit _ _ _ _

lemma bandCut_parent_identity :
    ((D.bandCutDiagram q).parentWord (.inr ())).eval φ (D.bandCutValues q g J T h)=1 := by
  unfold parentWord
  rw [Term.eval_cast_unit]
  exact map_one (rebaseUnit ((D.bandCutDiagram q).seamRank (.inr ())))

lemma bandCut_seam_last (s : S) :
    ((D.bandCutDiagram q).seamLeft (.inl (s,2))).eval φ (D.bandCutValues q g J T h)=
      (D.seamLeft s).eval φ g ∧
    ((D.bandCutDiagram q).seamRight (.inl (s,2))).eval φ (D.bandCutValues q g J T h)=
      (D.seamRight s).eval φ g := by
  constructor
  · simp only [seamLeft,Term.eval]
    rw [D.bandCut_parent_inl]
    let P : D.BandCutUnit (A:=A) s := rebaseUnit (D.seamRank s)
      (D.bandCutSideValues q g J T ⟨.inl (s,2),none⟩)
    let F (e : Bool) : D.BandCutUnit (A:=A) s := D.bandCutFrameValues q g J T (.inl (s,2)) e
    change P * F false = _
    have hl : (D.parentWord s).eval φ g = D.bandCutP s g := by
      unfold parentWord
      rw [Term.eval_cast_unit]
      rfl
    rw [hl]
    change P * F false = D.bandCutP s g * D.bandCutF s g false
    by_cases hs : s=q
    · subst s
      have hp : P=1 := by
        have hv : D.bandCutSideValues q g J T ⟨.inl (q,2),none⟩=1 := by
          simp [bandCutSideValues]
        dsimp only [P]
        erw [hv,map_one]
        rfl
      have hf : F false = D.bandCutP q g * D.bandCutF q g false := by
        dsimp only [F]
        simp [bandCutFrameValues]
      rw [hp,hf,one_mul]
    · have hp : P=D.bandCutP s g := by
        have hv : D.bandCutSideValues q g J T ⟨.inl (s,2),none⟩=g (.side ⟨s,none⟩) := by
          simp only [bandCutSideValues,dite_eq_right hs]
          rfl
        dsimp only [P]
        erw [hv]
        rfl
      have hf : F false=D.bandCutF s g false := by
        dsimp only [F]
        simp only [bandCutFrameValues,dite_eq_right hs]
        rfl
      rw [hp,hf]
  · simp only [seamRight,frameWord,childWord,sideWord,Term.eval,bandCutValues,
      bandCutSideValues]
    congr 1
    by_cases hs : s=q
    · subst s
      simp [bandCutFrameValues]
      rfl
    · simp [bandCutFrameValues,hs]
      rfl

lemma bandCut_seam_first (s : S) :
    ((D.bandCutDiagram q).seamLeft (.inl (s,0))).eval φ (D.bandCutValues q g J T h)=
      ((D.bandCutDiagram q).seamRight (.inl (s,0))).eval φ (D.bandCutValues q g J T h) := by
  simp only [seamLeft,seamRight,Term.eval]
  rw [D.bandCut_parent_inl]
  let P : D.BandCutUnit (A:=A) s := rebaseUnit (D.seamRank s)
    (D.bandCutSideValues q g J T ⟨.inl (s,0),none⟩)
  let F (e : Bool) : D.BandCutUnit (A:=A) s := D.bandCutFrameValues q g J T (.inl (s,0)) e
  let B : D.BandCutUnit (A:=A) s := blockUnit (D.childDim s)
    (fun j => (D.bandCutSideValues q g J T ⟨.inl (s,0),some j⟩)⁻¹)
  change P * F false = F true * B
  have hp : P=1 := by
    have hv : D.bandCutSideValues q g J T ⟨.inl (s,0),none⟩=1 := by
      by_cases hs : s=q
      · subst s; simp [bandCutSideValues]
      · simp only [bandCutSideValues,dite_eq_right hs]; rfl
    dsimp only [P]
    erw [hv,map_one]
    rfl
  have hb : B=1 := by
    have hc (j) : D.bandCutSideValues q g J T ⟨.inl (s,0),some j⟩=1 := rfl
    dsimp only [B]
    simp only [hc]
    convert! blockUnit_one (A:=A) (D.childDim s) using 1
  rw [hp,hb,one_mul,mul_one]
  dsimp only [F]
  by_cases hs : s=q
  · subst s; simp [bandCutFrameValues]; rfl
  · simp only [bandCutFrameValues,dite_eq_right hs]; rfl

lemma bandCut_seam_middle (s : S) :
    ((D.bandCutDiagram q).seamLeft (.inl (s,1))).eval φ (D.bandCutValues q g J T h)=
      ((D.bandCutDiagram q).seamRight (.inl (s,1))).eval φ (D.bandCutValues q g J T h) := by
  simp only [seamLeft,seamRight,Term.eval]
  rw [D.bandCut_parent_inl]
  let P : D.BandCutUnit (A:=A) s := rebaseUnit (D.seamRank s)
    (D.bandCutSideValues q g J T ⟨.inl (s,1),none⟩)
  let F (e : Bool) : D.BandCutUnit (A:=A) s := D.bandCutFrameValues q g J T (.inl (s,1)) e
  let B : D.BandCutUnit (A:=A) s := blockUnit (D.childDim s)
    (fun j => (D.bandCutSideValues q g J T ⟨.inl (s,1),some j⟩)⁻¹)
  change P * F false = F true * B
  have hb : B=1 := by
    have hc (j) : D.bandCutSideValues q g J T ⟨.inl (s,1),some j⟩=1 := rfl
    dsimp only [B]
    simp only [hc]
    convert! blockUnit_one (A:=A) (D.childDim s) using 1
  rw [hb,mul_one]
  by_cases hs : s=q
  · subst s
    have hp : P=T⁻¹*J⁻¹*D.bandCutP q g*T := by
      have hv : D.bandCutSideValues q g J T ⟨.inl (q,1),none⟩=
          rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T) := by
        simp [bandCutSideValues]
        rfl
      dsimp only [P]
      erw [hv,rebaseUnit_trans,rebaseUnit_refl]
    have hf0 : F false=T⁻¹*D.bandCutF q g false := by
      dsimp only [F]
      simp [bandCutFrameValues]
    have hf1 : F true=T⁻¹*J⁻¹*D.bandCutP q g*D.bandCutF q g false := by
      dsimp only [F]
      simp [bandCutFrameValues]
    rw [hp,hf0,hf1]
    group
  · have hp : P=1 := by
      have hv : D.bandCutSideValues q g J T ⟨.inl (s,1),none⟩=1 := by
        simp only [bandCutSideValues,dite_eq_right hs]; rfl
      dsimp only [P]
      erw [hv,map_one]
      rfl
    rw [hp,one_mul]
    dsimp only [F]
    simp only [bandCutFrameValues,dite_eq_right hs]
    rfl

end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ δ ε ζ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [Fintype δ] [Fintype ε] [Fintype ζ]
lemma reindex_reindex (x : MatrixIso R α β) (a : γ ≃ α) (b : δ ≃ β)
    (c : ε ≃ γ) (d : ζ ≃ δ) :
    (x.reindex a b).reindex c d=x.reindex (c.trans a) (d.trans b) := by
  apply ext <;> rfl
lemma unit_injective_general [DecidableEq α] : Function.Injective (unit (R:=R) (α:=α)) := by
  intro x y h
  exact congrArg toUnit h
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

lemma bandCut_identity_block :
    MatrixIso.unit (blockUnit ((D.bandCutDiagram q).childDim (.inr ()))
      (fun i => (((D.bandCutDiagram q).childWord (.inr ()) i).eval φ
        (D.bandCutValues q g J T h))⁻¹))=
      (MatrixIso.unit J⁻¹).reindex (D.bandCutIdentityColumns q) (D.bandCutIdentityColumns q) := by
  change MatrixIso.unit (blockUnit (fun _ : Fin 1 => D.rank (D.bandCutParent q))
    (fun _ => (rebaseUnit (D.seamRank q).symm J)⁻¹))=_
  erw [← map_inv,blockUnit_single,rebaseUnit_iso,MatrixIso.reindex_reindex]

lemma bandCut_seam_identity :
    ((D.bandCutDiagram q).seamLeft (.inr ())).eval φ (D.bandCutValues q g J T h)=
      ((D.bandCutDiagram q).seamRight (.inr ())).eval φ (D.bandCutValues q g J T h) := by
  simp only [seamLeft,seamRight,Term.eval]
  rw [D.bandCut_parent_identity q φ g J T h,one_mul]
  apply MatrixIso.unit_injective_general
  erw [MatrixIso.unit_mul]
  erw [D.bandCut_identity_block]
  simp only [frameWord,Term.eval,bandCutValues,bandCutFrameValues,ite_true,Bool.false_eq_true,ite_false,
    MatrixIso.unit_toUnit]
  rw [← MatrixIso.reindex_trans _ _ (D.bandCutIdentityColumns q)
    (D.bandCutIdentityColumns q) (finCongr (D.bandCutIdentityRank q))]
  rw [← MatrixIso.unit_mul]
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

lemma bandCut_vertexRanks_old (v : V) :
    (D.bandCutDiagram q).vertexRanks (.inl v)=D.vertexRanks v := rfl

lemma bandCutFrameValues_outer (s : S) (e : Bool) :
    D.bandCutFrameValues q g J T (.inl (s,if e then 2 else 0)) e=g (.frame s e) := by
  by_cases hs : s=q
  · subst s; cases e <;> simp [bandCutFrameValues] <;> rfl
  · cases e <;> simp only [bandCutFrameValues,dite_eq_right hs] <;> rfl

lemma bandCut_portFrame_old (p : LocalPort V D.ports.kind) :
    (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inl p.1,p.2⟩=
      D.portFrame g p := by
  change (MatrixIso.unit (D.bandCutFrameValues q g J T
    (.inl ((D.ports.attach p).1,if (D.ports.attach p).2 then 2 else 0))
    (D.ports.attach p).2)).reindex (D.portColumnIndex p) (D.portRowIndex p)=_
  rw [D.bandCutFrameValues_outer q g J T]

  rfl

lemma bandCut_vertexComparison_old (v : V) :
    (D.bandCutDiagram q).vertexComparison (D.bandCutValues q g J T h) (.inl v)=
      D.vertexComparison g v := by
  change VertexTable.LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v)
    (fun p => (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inl v,p⟩)=_
  exact congrArg (VertexTable.LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v))
    (funext fun p => D.bandCut_portFrame_old q g J T h ⟨v,p⟩)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)

lemma bandCut_vertexComparison_continuation (s : {s : S // s≠q}) (b : Bool) :
    ((D.bandCutDiagram q).vertexComparison (D.bandCutValues q g J T h) (.inr (.inl (s,b)))).Holds := by
  apply (MatrixIso.sameFramedFlag_iff _ _ _).mpr
  have H : ((D.bandCutDiagram q).vertexComparison (D.bandCutValues q g J T h) (.inr (.inl (s,b)))).left=
      ((D.bandCutDiagram q).vertexComparison (D.bandCutValues q g J T h) (.inr (.inl (s,b)))).right := by
    apply MatrixIso.ext <;> ext i j
    all_goals
      cases b <;> simp [vertexComparison,VertexTable.LocalRanks.comparison,
        VertexTable.LocalRanks.passageComparison,portFrame,bandCutValues,bandCutDiagram,
        bandCutPorts,bandCutAttach,bandCutAttachTo,bandCutFrameValues,s.property,
        MatrixIso.unit,MatrixIso.reindex] <;> rfl

  rw [H]
  intro i j _
  rw [MatrixIso.inv_val]
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {b : ℕ}
variable (d : LocalRanks (.splitting 0 b 0 false))
local instance : Fintype (d.Columns .before) := d.fintypeColumns .before
local instance : Fintype (d.Columns .after) := d.fintypeColumns .after
local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch

def fullSplitAfter : d.Columns .after ≃ d.SplitB where
  toFun | ⟨.inr (.inl i),j⟩ => ⟨i,j⟩
  invFun | ⟨i,j⟩ => ⟨.inr (.inl i),j⟩
  left_inv := by rintro ⟨i,j⟩; rcases i with i|i|i; exact Fin.elim0 i; rfl; exact Fin.elim0 i
  right_inv := by rintro ⟨i,j⟩; rfl

def fullSplitBefore : d.Columns .before ≃ d.SplitW where
  toFun | ⟨.inr (.inl ()),j⟩ => j
  invFun j := ⟨.inr (.inl ()),j⟩
  left_inv := by rintro ⟨i,j⟩; rcases i with i|u|i; exact Fin.elim0 i; cases u; rfl; exact Fin.elim0 i
  right_inv _ := rfl

/-- Refinement of the sole block at the inverse-band vertices. -/
lemma splitRefinement_full (w : MatrixIso R (d.Columns .branch) (d.Parent .branch)) :
    d.splitRefinement w=(w.reindex d.splitBranchChildren d.splitBranchParent).reindex
      d.fullSplitAfter d.fullSplitBefore := by
  apply MatrixIso.ext
  · ext ⟨i,j⟩ ⟨k,l⟩
    rcases i with i|u|i
    · exact Fin.elim0 i
    · cases u
      rcases k with k|k|k
      · exact Fin.elim0 k
      · rfl
      · exact Fin.elim0 k
    · exact Fin.elim0 i
  · ext ⟨i,j⟩ ⟨k,l⟩
    rcases i with i|i|i
    · exact Fin.elim0 i
    · rcases k with k|u|k
      · exact Fin.elim0 k
      · cases u; rfl
      · exact Fin.elim0 k
    · exact Fin.elim0 i
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
lemma rank_ext {k : Kind} (d e : LocalRanks k) (h : d.rank=e.rank) : d=e := by
  cases d; cases e; cases h; rfl
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression VertexTable
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)

abbrev bandCutSplitRanks : LocalRanks (.splitting 0 (arity q) 0 false) :=
  (D.bandCutDiagram q).vertexRanks (.inr (.inr false))

lemma bandCutSplitRanks_reverse :
    ((D.bandCutDiagram q).vertexRanks (.inr (.inr true))).forwardRanks=D.bandCutSplitRanks q := by
  apply LocalRanks.rank_ext
  funext p c
  cases p <;> rfl

/-- After and branch fiber indices in the full-block split. -/
def bandCutSplitChildIndex : (D.bandCutSplitRanks q).Columns .branch ≃ Fin (D.seamDim q) :=
  (blockIndex (D.childDim q)).symm

def bandCutSplitRowIndex : (D.bandCutSplitRanks q).Parent .branch ≃ Fin (D.seamDim q) :=
  finCongr (D.seamRank q)

def bandCutSplitParentIndex : (D.bandCutSplitRanks q).Parent .before ≃ Fin (D.seamDim q) :=
  finCongr (D.seamRank q)

lemma bandCutSplitChild_compat :
    ((D.bandCutSplitRanks q).fullSplitAfter.trans (D.bandCutSplitRanks q).splitBranchChildren).trans
      (D.bandCutSplitChildIndex q)=
    (D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.after⟩ := by
  apply Equiv.ext
  rintro ⟨i,j⟩
  rcases i with i|i|i
  · exact Fin.elim0 i
  · change (blockIndex (D.childDim q)).symm
      ((D.bandCutSplitRanks q).splitBranchChildren ((D.bandCutSplitRanks q).fullSplitAfter ⟨.inr (.inl i),j⟩))=
      (blockIndex (D.childDim q)).symm
        (((D.ports.bandCutPorts q).childEquiv ⟨.inr (.inr false),.after⟩).sigmaCongr
          (fun _ => Equiv.refl _) ⟨.inr (.inl i),j⟩)
    apply congrArg (blockIndex (D.childDim q)).symm
    apply Sigma.ext
    · apply Fin.ext
      change i.val = 0+(i.val+0)
      omega
    · apply (Fin.heq_ext_iff (congrArg (D.childDim q) (by
        apply Fin.ext
        change i.val = 0+(i.val+0)
        omega))).mpr
      rfl
  · exact Fin.elim0 i

lemma bandCutSplitBefore_compat :
    ((D.bandCutSplitRanks q).fullSplitBefore.trans (D.bandCutSplitRanks q).splitBranchParent).trans
      (D.bandCutSplitRowIndex q)=
    ((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.before⟩).trans
      (D.bandCutIdentityColumns q) := by
  apply Equiv.ext
  rintro ⟨i,j⟩
  rcases i with i|u|i
  · exact Fin.elim0 i
  · cases u
    apply Fin.ext
    have hc : (blockIndex ((D.bandCutDiagram q).childDim (.inr ())))
        (((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.before⟩) ⟨.inr (.inl ()),j⟩)=
      (((D.ports.bandCutPorts q).childEquiv ⟨.inr (.inr false),.before⟩).sigmaCongr
          (fun _ => Equiv.refl _) ⟨.inr (.inl ()),j⟩) := Equiv.apply_symm_apply _ _
    change j.val =
      ((Equiv.uniqueSigma (fun _ : Fin 1 => Fin (D.rank (D.bandCutParent q))))
        ((blockIndex ((D.bandCutDiagram q).childDim (.inr ())))
          (((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.before⟩) ⟨.inr (.inl ()),j⟩))).val
    erw [hc,uniqueSigma_const_apply]
    rfl
  · exact Fin.elim0 i
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport VertexTable
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)

local instance (p : SplitPort) : Fintype ((D.bandCutSplitRanks q).Columns p) :=
  (D.bandCutSplitRanks q).fintypeColumns p

abbrev bandCutSplitFrame (M B : D.BandCutUnit (A:=A) q) :
    ∀ p, MatrixIso A ((D.bandCutSplitRanks q).Columns p) ((D.bandCutSplitRanks q).Parent p)
  | .before => (MatrixIso.unit M).reindex
      (((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.before⟩).trans (D.bandCutIdentityColumns q))
      (((D.bandCutDiagram q).portRowIndex ⟨.inr (.inr false),.before⟩).trans (finCongr (D.bandCutIdentityRank q)))
  | .after => (MatrixIso.unit (M*B)).reindex
      ((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.after⟩)
      ((D.bandCutDiagram q).portRowIndex ⟨.inr (.inr false),.after⟩)
  | .branch => (MatrixIso.unit B).reindex (D.bandCutSplitChildIndex q) (D.bandCutSplitRowIndex q)

lemma bandCutSplitFrame_exact (M B : D.BandCutUnit (A:=A) q) :
    ((D.bandCutSplitRanks q).splitComparison (D.bandCutSplitFrame q M B)).left=
    ((D.bandCutSplitRanks q).splitComparison (D.bandCutSplitFrame q M B)).right := by
  change (D.bandCutSplitFrame q M B .after)=
    (((D.bandCutSplitRanks q).splitRefinement (D.bandCutSplitFrame q M B .branch)).trans
      (D.bandCutSplitFrame q M B .before)).reindex (Equiv.refl _) (D.bandCutSplitRanks q).splitParent
  rw [LocalRanks.splitRefinement_full]
  simp only [bandCutSplitFrame,MatrixIso.reindex_reindex]
  rw [show (D.bandCutSplitRanks q).fullSplitAfter.trans
      ((D.bandCutSplitRanks q).splitBranchChildren.trans (D.bandCutSplitChildIndex q))=
      (D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.after⟩ from D.bandCutSplitChild_compat q]
  rw [show (D.bandCutSplitRanks q).fullSplitBefore.trans
      ((D.bandCutSplitRanks q).splitBranchParent.trans (D.bandCutSplitRowIndex q))=
      ((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr false),.before⟩).trans
        (D.bandCutIdentityColumns q) from D.bandCutSplitBefore_compat q]
  erw [← MatrixIso.reindex_trans,← MatrixIso.unit_mul,MatrixIso.reindex_reindex]
  congr 1
end IntegralCharacterVarieties.SurfacePresentation.Diagram
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport VertexTable
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
local instance (p : SplitPort) : Fintype ((D.bandCutSplitRanks q).Columns p) :=
  (D.bandCutSplitRanks q).fintypeColumns p

lemma bandCut_portFrame_first (p : SplitPort) :
    (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inr (.inr false),p⟩=
      D.bandCutSplitFrame q T⁻¹ (D.bandCutF q g false) p := by
  cases p with
  | before =>
    change (MatrixIso.unit (((MatrixIso.unit T⁻¹).reindex (D.bandCutIdentityColumns q)
      (finCongr (D.bandCutIdentityRank q))).toUnit)).reindex _ _ = _
    erw [MatrixIso.unit_toUnit,MatrixIso.reindex_reindex]
    rfl
  | after =>
    change (MatrixIso.unit (D.bandCutFrameValues q g J T (.inl (q,1)) false)).reindex _ _ = _
    simp only [bandCutFrameValues,show (1:Fin 3)≠0 by decide,ite_true,
      Bool.false_eq_true]
    rfl
  | branch =>
    change (MatrixIso.unit (D.bandCutFrameValues q g J T (.inl (q,0)) true)).reindex _ _ = _
    simp only [bandCutFrameValues]
    rfl

lemma bandCut_vertexComparison_first :
    ((D.bandCutDiagram q).vertexComparison (D.bandCutValues q g J T h) (.inr (.inr false))).Holds := by
  change ((D.bandCutSplitRanks q).splitComparison
    (fun p => (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inr (.inr false),p⟩)).Holds
  erw [show (fun p => (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inr (.inr false),p⟩)=
    D.bandCutSplitFrame q T⁻¹ (D.bandCutF q g false) from funext (D.bandCut_portFrame_first q g J T h)]
  unfold FlagComparison.Holds
  rw [D.bandCutSplitFrame_exact q T⁻¹ (D.bandCutF q g false)]
  exact MatrixIso.holds_self _ _
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression VertexTable
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)

abbrev bandCutSplitRanksLast : LocalRanks (.splitting 0 (arity q) 0 false) :=
  ((D.bandCutDiagram q).vertexRanks (.inr (.inr true))).forwardRanks

/-- After and branch fiber indices in the full-block split. -/
def bandCutSplitChildIndexLast : (D.bandCutSplitRanksLast q).Columns .branch ≃ Fin (D.seamDim q) :=
  (blockIndex (D.childDim q)).symm

def bandCutSplitRowIndexLast : (D.bandCutSplitRanksLast q).Parent .branch ≃ Fin (D.seamDim q) :=
  finCongr (D.seamRank q)

def bandCutSplitParentIndexLast : (D.bandCutSplitRanksLast q).Parent .before ≃ Fin (D.seamDim q) :=
  finCongr (D.seamRank q)

lemma bandCutSplitChild_compatLast :
    ((D.bandCutSplitRanksLast q).fullSplitAfter.trans (D.bandCutSplitRanksLast q).splitBranchChildren).trans
      (D.bandCutSplitChildIndexLast q)=
    (D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.after⟩ := by
  apply Equiv.ext
  rintro ⟨i,j⟩
  rcases i with i|i|i
  · exact Fin.elim0 i
  · change (blockIndex (D.childDim q)).symm
      ((D.bandCutSplitRanksLast q).splitBranchChildren ((D.bandCutSplitRanksLast q).fullSplitAfter ⟨.inr (.inl i),j⟩))=
      (blockIndex (D.childDim q)).symm
        (((D.ports.bandCutPorts q).childEquiv ⟨.inr (.inr true),.after⟩).sigmaCongr
          (fun _ => Equiv.refl _) ⟨.inr (.inl i),j⟩)
    apply congrArg (blockIndex (D.childDim q)).symm
    apply Sigma.ext
    · apply Fin.ext
      change i.val = 0+(i.val+0)
      omega
    · apply (Fin.heq_ext_iff (congrArg (D.childDim q) (by
        apply Fin.ext
        change i.val = 0+(i.val+0)
        omega))).mpr
      rfl
  · exact Fin.elim0 i

lemma bandCutSplitBefore_compatLast :
    ((D.bandCutSplitRanksLast q).fullSplitBefore.trans (D.bandCutSplitRanksLast q).splitBranchParent).trans
      (D.bandCutSplitRowIndexLast q)=
    ((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.before⟩).trans
      (D.bandCutIdentityColumns q) := by
  apply Equiv.ext
  rintro ⟨i,j⟩
  rcases i with i|u|i
  · exact Fin.elim0 i
  · cases u
    apply Fin.ext
    have hc : (blockIndex ((D.bandCutDiagram q).childDim (.inr ())))
        (((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.before⟩) ⟨.inr (.inl ()),j⟩)=
      (((D.ports.bandCutPorts q).childEquiv ⟨.inr (.inr true),.before⟩).sigmaCongr
          (fun _ => Equiv.refl _) ⟨.inr (.inl ()),j⟩) := Equiv.apply_symm_apply _ _
    change j.val =
      ((Equiv.uniqueSigma (fun _ : Fin 1 => Fin (D.rank (D.bandCutParent q))))
        ((blockIndex ((D.bandCutDiagram q).childDim (.inr ())))
          (((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.before⟩) ⟨.inr (.inl ()),j⟩))).val
    erw [hc,uniqueSigma_const_apply]
    rfl
  · exact Fin.elim0 i
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport VertexTable
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)

local instance (p : SplitPort) : Fintype ((D.bandCutSplitRanksLast q).Columns p) :=
  (D.bandCutSplitRanksLast q).fintypeColumns p

abbrev bandCutSplitFrameLast (M B : D.BandCutUnit (A:=A) q) :
    ∀ p, MatrixIso A ((D.bandCutSplitRanksLast q).Columns p) ((D.bandCutSplitRanksLast q).Parent p)
  | .before => (MatrixIso.unit M).reindex
      (((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.before⟩).trans (D.bandCutIdentityColumns q))
      (((D.bandCutDiagram q).portRowIndex ⟨.inr (.inr true),.before⟩).trans (finCongr (D.bandCutIdentityRank q)))
  | .after => (MatrixIso.unit (M*B)).reindex
      ((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.after⟩)
      ((D.bandCutDiagram q).portRowIndex ⟨.inr (.inr true),.after⟩)
  | .branch => (MatrixIso.unit B).reindex (D.bandCutSplitChildIndexLast q) (D.bandCutSplitRowIndexLast q)

lemma bandCutSplitFrameLast_exact (M B : D.BandCutUnit (A:=A) q) :
    ((D.bandCutSplitRanksLast q).splitComparison (D.bandCutSplitFrameLast q M B)).left=
    ((D.bandCutSplitRanksLast q).splitComparison (D.bandCutSplitFrameLast q M B)).right := by
  change (D.bandCutSplitFrameLast q M B .after)=
    (((D.bandCutSplitRanksLast q).splitRefinement (D.bandCutSplitFrameLast q M B .branch)).trans
      (D.bandCutSplitFrameLast q M B .before)).reindex (Equiv.refl _) (D.bandCutSplitRanksLast q).splitParent
  rw [LocalRanks.splitRefinement_full]
  simp only [bandCutSplitFrameLast,MatrixIso.reindex_reindex]
  rw [show (D.bandCutSplitRanksLast q).fullSplitAfter.trans
      ((D.bandCutSplitRanksLast q).splitBranchChildren.trans (D.bandCutSplitChildIndexLast q))=
      (D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.after⟩ from D.bandCutSplitChild_compatLast q]
  rw [show (D.bandCutSplitRanksLast q).fullSplitBefore.trans
      ((D.bandCutSplitRanksLast q).splitBranchParent.trans (D.bandCutSplitRowIndexLast q))=
      ((D.bandCutDiagram q).portColumnIndex ⟨.inr (.inr true),.before⟩).trans
        (D.bandCutIdentityColumns q) from D.bandCutSplitBefore_compatLast q]
  erw [← MatrixIso.reindex_trans,← MatrixIso.unit_mul,MatrixIso.reindex_reindex]
  congr 1
end IntegralCharacterVarieties.SurfacePresentation.Diagram
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport VertexTable
variable {F S V A : Type} {arity : S → ℕ} [CommRing A]
variable (D : Diagram F S V arity) (q : S)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool →
      (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ)
local instance (p : SplitPort) : Fintype ((D.bandCutSplitRanksLast q).Columns p) :=
  (D.bandCutSplitRanksLast q).fintypeColumns p

lemma bandCut_portFrame_last (p : SplitPort) :
    (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inr (.inr true),p⟩=
      D.bandCutSplitFrameLast q (T⁻¹*J⁻¹) (D.bandCutP q g*D.bandCutF q g false) p := by
  cases p with
  | before =>
    change (MatrixIso.unit (((MatrixIso.unit (T⁻¹*J⁻¹)).reindex (D.bandCutIdentityColumns q)
      (finCongr (D.bandCutIdentityRank q))).toUnit)).reindex _ _ = _
    erw [MatrixIso.unit_toUnit,MatrixIso.reindex_reindex]
    rfl
  | after =>
    change (MatrixIso.unit (D.bandCutFrameValues q g J T (.inl (q,1)) true)).reindex _ _ = _
    simp only [bandCutFrameValues,show (1:Fin 3)≠0 by decide,ite_true]
    rw [mul_assoc]
    rfl
  | branch =>
    change (MatrixIso.unit (D.bandCutFrameValues q g J T (.inl (q,2)) false)).reindex _ _ = _
    simp only [bandCutFrameValues,show (2:Fin 3)≠0 by decide,
      show (2:Fin 3)≠1 by decide,ite_false,Bool.false_eq_true]
    rfl

lemma bandCut_vertexComparison_last :
    ((D.bandCutDiagram q).vertexComparison (D.bandCutValues q g J T h) (.inr (.inr true))).Holds := by
  change ((D.bandCutSplitRanksLast q).splitComparison
    (fun p => (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inr (.inr true),p⟩)).Holds
  erw [show (fun p => (D.bandCutDiagram q).portFrame (D.bandCutValues q g J T h) ⟨.inr (.inr true),p⟩)=
    D.bandCutSplitFrameLast q (T⁻¹*J⁻¹) (D.bandCutP q g*D.bandCutF q g false) from
      funext (D.bandCut_portFrame_last q g J T h)]
  unfold FlagComparison.Holds
  rw [D.bandCutSplitFrameLast_exact q (T⁻¹*J⁻¹) (D.bandCutP q g*D.bandCutF q g false)]
  exact MatrixIso.holds_self _ _
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
