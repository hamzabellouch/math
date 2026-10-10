import OAI.AlgebraicGeometry.CharacterVarieties.Seams.CutWords

namespace OAI

/-!
# Handles and boundary gauges for a cut

The retained handle coordinates and boundary gauges determine the new
transport values for inverse nonseparating surgery.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S)

abbrev FacetUnit (f : F) := (Matrix (Fin (D.rank f)) (Fin (D.rank f)) A)ˣ

/-- Retain the old handle slots after deleting the last handle on the chosen parent. -/
def bandCutHandleIndex (f : F) (k : Fin ((D.bandCutDiagram q).genus f)) : Fin (D.genus f) :=
  ⟨k.val,by
    have hk := k.isLt
    change k.val < (if f=D.bandCutParent q then D.genus f-1 else D.genus f) at hk
    split at hk <;> omega⟩

def bandCutHandleBase (t : D.FacetUnit (A:=A) (D.bandCutParent q)) (f : F) : D.FacetUnit (A:=A) f :=
  if hf : f=D.bandCutParent q then by subst f; exact t⁻¹ else 1

def bandCutRetainedHandles
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (t : D.FacetUnit (A:=A) (D.bandCutParent q))
    (f : F) (k : Fin ((D.bandCutDiagram q).genus f)) (b : Bool) : D.FacetUnit (A:=A) f :=
  D.bandCutHandleBase q t f*(show D.FacetUnit (A:=A) f from g (.handle f (D.bandCutHandleIndex q f k) b))*(D.bandCutHandleBase q t f)⁻¹

/-- Boundary gauges determined by the old boundary order. -/
def bandCutCircleBases (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (U V : D.FacetUnit (A:=A) (D.bandCutParent q)) : D.CircleBases (R:=A) := fun B =>
  if hf : B.1=D.bandCutParent q then by
    rcases B with ⟨f,b⟩
    dsimp at hf
    subst f
    exact MatrixIso.unit (if b.val < b0.val then U else if b0.val < b.val then V else 1)
  else MatrixIso.refl

variable (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
variable (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
variable (t a : D.FacetUnit (A:=A) (D.bandCutParent q))

/-- The transport along the new seam with an identity child. -/
def bandCutChosenJ : D.BandCutUnit (A:=A) q :=
  rebaseUnit (D.seamRank q)
    ((D.boundaryTail φ g _ b0 i0)⁻¹*a*(D.boundaryPrefix φ g _ b0 i0)⁻¹)

def bandCutChosenT : D.BandCutUnit (A:=A) q :=
  rebaseUnit (D.seamRank q) (D.boundaryPrefix φ g _ b0 i0*t)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
variable (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
variable (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)
variable (t a : D.FacetUnit (A:=A) (D.bandCutParent q))
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool → D.FacetUnit (A:=A) f)
include hb

lemma bandCutChosen_long :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inl b0))).eval φ
      (D.bandCutValues q g (D.bandCutChosenJ q φ g b0 i0 a) (D.bandCutChosenT q φ g b0 i0 t) h) = a := by
  rw [D.bandCutBoundaryWord_selected q φ g _ _ h b0 i0 hb]
  unfold bandCutChosenJ
  rw [rebaseUnit_trans]
  change D.boundaryTail φ g _ b0 i0 *
    ((D.boundaryTail φ g _ b0 i0)⁻¹*a*(D.boundaryPrefix φ g _ b0 i0)⁻¹)*
      D.boundaryPrefix φ g _ b0 i0 = a
  group

lemma bandCutChosen_short (j : Fin (D.bandCutExtra q (D.bandCutParent q))) :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inr j))).eval φ
      (D.bandCutValues q g (D.bandCutChosenJ q φ g b0 i0 a) (D.bandCutChosenT q φ g b0 i0 t) h) =
      t⁻¹*a⁻¹*(D.boundaryWord (D.bandCutParent q) b0).eval φ g*t := by
  erw [bandCutBoundaryWord_short]
  rw [D.boundaryWord_split φ g _ b0 i0,D.bandCutChosenEdge q φ g b0 i0 hb]
  have transport {m n : ℕ} (hn : m=n)
      (u v x y : (Matrix (Fin m) (Fin m) A)ˣ)
      (p : (Matrix (Fin n) (Fin n) A)ˣ) :
      rebaseUnit hn.symm
        ((rebaseUnit hn (u*y))⁻¹ * (rebaseUnit hn (v⁻¹*x*u⁻¹))⁻¹ * p *
          rebaseUnit hn (u*y)) = y⁻¹*x⁻¹*(v*rebaseUnit hn.symm p*u)*y := by
    subst n
    simp only [rebaseUnit_refl]
    group
  convert! transport (D.seamRank q) (D.boundaryPrefix φ g _ b0 i0)
    (D.boundaryTail φ g _ b0 i0) a t (D.bandCutP q g) using 1

omit hb in
lemma bandCutCircleBases_parent (U V : D.FacetUnit (A:=A) (D.bandCutParent q))
    (b : Fin (D.boundaryCount (D.bandCutParent q))) :
    (D.bandCutCircleBases q b0 U V) ⟨D.bandCutParent q,b⟩ =
      MatrixIso.unit (if b.val < b0.val then U else if b0.val < b.val then V else 1) := by
  simp [bandCutCircleBases]

omit hb in
lemma bandCutCircleBases_other (U V : D.FacetUnit (A:=A) (D.bandCutParent q))
    (f : F) (hf : f≠D.bandCutParent q) (b : Fin (D.boundaryCount f)) :
    (D.bandCutCircleBases q b0 U V) ⟨f,b⟩ = MatrixIso.refl := by
  unfold bandCutCircleBases
  simp only [dite_eq_right hf]
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (t : D.FacetUnit (A:=A) (D.bandCutParent q))

/-- The ordered product of the retained handle commutators. -/
def bandCutRetainedProduct (f : F) : D.FacetUnit (A:=A) f :=
  (List.ofFn fun k => (D.commutatorWord f (D.bandCutHandleIndex q f k)).eval φ g).prod

lemma bandCutCommutator_eval (f : F) (k : Fin ((D.bandCutDiagram q).genus f)) :
    ((D.bandCutDiagram q).commutatorWord f k).eval φ
      (D.bandCutValues q g J T (D.bandCutRetainedHandles q g t)) =
    D.bandCutHandleBase q t f*(D.commutatorWord f (D.bandCutHandleIndex q f k)).eval φ g*
      (D.bandCutHandleBase q t f)⁻¹ := by
  simp only [commutatorWord,Term.eval,bandCutValues,bandCutRetainedHandles]
  let u : D.FacetUnit (A:=A) f := D.bandCutHandleBase q t f
  let x : D.FacetUnit (A:=A) f := g (.handle f (D.bandCutHandleIndex q f k) false)
  let y : D.FacetUnit (A:=A) f := g (.handle f (D.bandCutHandleIndex q f k) true)
  change (u*x*u⁻¹)*(u*y*u⁻¹)*(u*x*u⁻¹)⁻¹*(u*y*u⁻¹)⁻¹ =
    u*(x*y*x⁻¹*y⁻¹)*u⁻¹
  group

lemma bandCutHandleProduct_eval (f : F) :
    (List.ofFn fun k => ((D.bandCutDiagram q).commutatorWord f k).eval φ
      (D.bandCutValues q g J T (D.bandCutRetainedHandles q g t))).prod =
    D.bandCutHandleBase q t f*D.bandCutRetainedProduct q φ g f*(D.bandCutHandleBase q t f)⁻¹ := by
  simp_rw [bandCutCommutator_eval]
  have hh := map_list_prod (MulAut.conj (D.bandCutHandleBase q t f))
    (List.ofFn fun k => (D.commutatorWord f (D.bandCutHandleIndex q f k)).eval φ g)
  simp only [List.map_ofFn,Function.comp_def,MulAut.conj_apply] at hh
  convert! hh.symm using 1

lemma bandCutHandleBase_parent : D.bandCutHandleBase q t (D.bandCutParent q)=t⁻¹ := by
  simp [bandCutHandleBase]

lemma bandCutHandleBase_other (f : F) (hf : f≠D.bandCutParent q) :
    D.bandCutHandleBase q t f=1 := by
  unfold bandCutHandleBase
  simp only [dite_eq_right hf]

variable (hg : 0 < D.genus (D.bandCutParent q))

def bandCutLastHandle : Fin (D.genus (D.bandCutParent q)) :=
  ⟨(D.bandCutDiagram q).genus (D.bandCutParent q),by
    have he := D.bandCutDiagram_genus_drop q hg
    omega⟩

lemma bandCutOldHandleProduct_parent :
    (List.ofFn fun k => (D.commutatorWord (D.bandCutParent q) k).eval φ g).prod =
      D.bandCutRetainedProduct q φ g (D.bandCutParent q)*
        (D.commutatorWord (D.bandCutParent q) (D.bandCutLastHandle q hg)).eval φ g := by
  rw [List.ofFn_congr (D.bandCutDiagram_genus_drop q hg).symm,List.ofFn_succ_last]
  simp only [List.prod_append,List.prod_cons,List.prod_nil,mul_one]
  rfl

lemma bandCutOldHandleProduct_other (f : F) (hf : f≠D.bandCutParent q) :
    (List.ofFn fun k => (D.commutatorWord f k).eval φ g).prod =
      D.bandCutRetainedProduct q φ g f := by
  have he : D.genus f=(D.bandCutDiagram q).genus f := by simp [bandCutDiagram,hf]
  rw [List.ofFn_congr he]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
