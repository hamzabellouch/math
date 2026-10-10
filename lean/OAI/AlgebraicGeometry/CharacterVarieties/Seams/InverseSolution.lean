import OAI.AlgebraicGeometry.CharacterVarieties.Seams.Handles
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.DiskGauge

namespace OAI

/-!
# Solutions under inverse nonseparating surgery

The boundary and handle identities preserve the surface relations.
Together with the seam and vertex equations they define a solution over the coefficient algebra.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
variable (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
variable (t a : D.FacetUnit (A:=A) (D.bandCutParent q))

abbrev bandCutU := t⁻¹*(t*a*t⁻¹*a⁻¹)
abbrev bandCutV := t⁻¹*a⁻¹*(D.boundaryWord (D.bandCutParent q) b0).eval φ g

def bandCutLiftGauge : D.CircleBases (R:=A) :=
  D.bandCutCircleBases q b0 (D.bandCutU q t a) (D.bandCutV q φ g b0 t a)

def bandCutLiftGenerators := D.gaugeGenerators (D.bandCutLiftGauge q φ g b0 t a) g

def bandCutLiftValues : (e : (D.bandCutDiagram q).Generator) →
    (Matrix (Fin ((D.bandCutDiagram q).generatorRank e)) (Fin ((D.bandCutDiagram q).generatorRank e)) A)ˣ :=
  let g' := D.bandCutLiftGenerators q φ g b0 t a
  D.bandCutValues q g' (D.bandCutChosenJ q φ g' b0 i0 a) (D.bandCutChosenT q φ g' b0 i0 t)
    (D.bandCutRetainedHandles q g' t)

lemma bandCutLiftGauge_selected :
    (D.bandCutLiftGauge q φ g b0 t a) ⟨D.bandCutParent q,b0⟩=MatrixIso.unit 1 := by
  rw [bandCutLiftGauge,bandCutCircleBases_parent]
  simp

lemma bandCutLiftGenerators_selected :
    (D.boundaryWord (D.bandCutParent q) b0).eval φ (D.bandCutLiftGenerators q φ g b0 t a)=
      (D.boundaryWord (D.bandCutParent q) b0).eval φ g := by
  rw [bandCutLiftGenerators,boundaryWord_gauge,bandCutLiftGauge_selected,MatrixIso.toUnit_unit]
  simp

variable (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)
include hb

lemma bandCutLiftBoundary_selected :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inl b0))).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) = a :=
  D.bandCutChosen_long q φ _ b0 i0 hb t a _

lemma bandCutLiftBoundary_short (j : Fin (D.bandCutExtra q (D.bandCutParent q))) :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inr j))).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) =
      t⁻¹*a⁻¹*(D.boundaryWord (D.bandCutParent q) b0).eval φ g*t := by
  rw [bandCutLiftValues,D.bandCutChosen_short q φ _ b0 i0 hb,bandCutLiftGenerators_selected]

lemma bandCutLiftBoundary_parent (b : Fin (D.boundaryCount (D.bandCutParent q))) (hne : b≠b0) :
    ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inl b))).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) =
    (if b.val < b0.val then D.bandCutU q t a else D.bandCutV q φ g b0 t a)*
      (D.boundaryWord (D.bandCutParent q) b).eval φ g*
        (if b.val < b0.val then D.bandCutU q t a else D.bandCutV q φ g b0 t a)⁻¹ := by
  rw [bandCutLiftValues,D.bandCutBoundaryWord_other q φ _ _ _ _ b0 i0 hb]
  · rw [bandCutLiftGenerators,boundaryWord_gauge,bandCutLiftGauge,bandCutCircleBases_parent,
      MatrixIso.toUnit_unit]
    have hh : b.val≠b0.val := fun h => hne (Fin.ext h)
    by_cases hlt : b.val < b0.val
    · simp [hlt]
      rfl
    · have hgt : b0.val < b.val := by omega
      simp [hlt,hgt]
      rfl
  · simpa using hne

lemma bandCutLiftBoundary_other (f : F) (hf : f≠D.bandCutParent q) (b : Fin (D.boundaryCount f)) :
    ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inl b))).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) = (D.boundaryWord f b).eval φ g := by
  rw [bandCutLiftValues,D.bandCutBoundaryWord_other q φ _ _ _ _ b0 i0 hb]
  · rw [bandCutLiftGenerators,boundaryWord_gauge,bandCutLiftGauge,
      D.bandCutCircleBases_other q b0 _ _ f hf]
    have hrefl : (MatrixIso.refl : MatrixIso A (Fin (D.rank f)) (Fin (D.rank f))).toUnit=1 := by
      apply Units.ext
      ext i j
      simp [MatrixIso.toUnit, MatrixIso.refl, Matrix.one_apply]
    rw [hrefl]
    simp
    rfl
  · intro he
    exact hf (congrArg Sigma.fst he)
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
variable (t a : D.FacetUnit (A:=A) (D.bandCutParent q))

/-- The two ordered products on either side of the selected old circle. -/
def bandCutEarlier : D.FacetUnit (A:=A) (D.bandCutParent q) :=
  ((List.ofFn fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g).take b0.val).prod

def bandCutLater : D.FacetUnit (A:=A) (D.bandCutParent q) :=
  ((List.ofFn fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g).drop (b0.val+1)).prod

lemma bandCutOldBoundaryProduct_parent :
    (List.ofFn fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g).prod =
    D.bandCutEarlier q φ g b0*(D.boundaryWord (D.bandCutParent q) b0).eval φ g*D.bandCutLater q φ g b0 := by
  have hh := SurfaceSurgery.ofFn_three_regions
    (fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g)
    (fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g) b0 1 1
    ((D.boundaryWord (D.bandCutParent q) b0).eval φ g)
    (fun _ _ => by simp) rfl (fun _ _ => by simp)
  simpa only [one_mul,mul_one,inv_one,bandCutEarlier,bandCutLater] using hh

lemma bandCutBoundaryProduct_split
    (v : (e : (D.bandCutDiagram q).Generator) →
      (Matrix (Fin ((D.bandCutDiagram q).generatorRank e)) (Fin ((D.bandCutDiagram q).generatorRank e)) A)ˣ)
    (f : F) :
    (List.ofFn fun b => ((D.bandCutDiagram q).boundaryWord f b).eval φ v).prod =
      (List.ofFn fun b : Fin (D.boundaryCount f) =>
        ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inl b))).eval φ v).prod *
      (List.ofFn fun j : Fin (D.bandCutExtra q f) =>
        ((D.bandCutDiagram q).boundaryWord f (finSumFinEquiv (.inr j))).eval φ v).prod := by
  change (List.ofFn (fun b : Fin (D.boundaryCount f+D.bandCutExtra q f) => _)).prod = _
  rw [List.ofFn_add,List.prod_append]
  rfl

variable (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)
include hb

lemma bandCutBoundaryProduct_long_parent :
    (List.ofFn fun b : Fin (D.boundaryCount (D.bandCutParent q)) =>
      ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) (finSumFinEquiv (.inl b))).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a)).prod =
    (D.bandCutU q t a*D.bandCutEarlier q φ g b0*(D.bandCutU q t a)⁻¹)*a*
      (D.bandCutV q φ g b0 t a*D.bandCutLater q φ g b0*(D.bandCutV q φ g b0 t a)⁻¹) := by
  apply SurfaceSurgery.ofFn_three_regions
    (fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g)
  · intro b hlt
    rw [D.bandCutLiftBoundary_parent q φ g b0 i0 t a hb b]
    · simp [hlt]
    · intro he; subst b; omega
  · exact D.bandCutLiftBoundary_selected q φ g b0 i0 t a hb
  · intro b hgt
    rw [D.bandCutLiftBoundary_parent q φ g b0 i0 t a hb b]
    · have hn : ¬b.val < b0.val := by omega
      simp [hn]
    · intro he; subst b; omega

lemma bandCutBoundaryProduct_parent :
    (List.ofFn fun b => ((D.bandCutDiagram q).boundaryWord (D.bandCutParent q) b).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a)).prod =
    (D.bandCutU q t a*D.bandCutEarlier q φ g b0*(D.bandCutU q t a)⁻¹)*a*
      (D.bandCutV q φ g b0 t a*D.bandCutLater q φ g b0*(D.bandCutV q φ g b0 t a)⁻¹)*
      (t⁻¹*a⁻¹*(D.boundaryWord (D.bandCutParent q) b0).eval φ g*t) := by
  rw [bandCutBoundaryProduct_split,D.bandCutBoundaryProduct_long_parent q φ g b0 i0 t a hb]
  simp_rw [D.bandCutLiftBoundary_short q φ g b0 i0 t a hb]
  have he : D.bandCutExtra q (D.bandCutParent q)=1 := by simp [bandCutExtra]
  erw [List.ofFn_congr he]
  let v : D.FacetUnit (A:=A) (D.bandCutParent q) :=
    t⁻¹*a⁻¹*(D.boundaryWord (D.bandCutParent q) b0).eval φ g*t
  have hv : (List.ofFn (fun _ : Fin 1 => v)).prod = v := by simp
  erw [hv]
  rfl

lemma bandCutBoundaryProduct_other (f : F) (hf : f≠D.bandCutParent q) :
    (List.ofFn fun b => ((D.bandCutDiagram q).boundaryWord f b).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a)).prod =
    (List.ofFn fun b => (D.boundaryWord f b).eval φ g).prod := by
  rw [bandCutBoundaryProduct_split]
  simp_rw [D.bandCutLiftBoundary_other q φ g b0 i0 t a hb f hf]
  have he : D.bandCutExtra q f=0 := by simp [bandCutExtra,hf]
  erw [List.ofFn_congr he]
  simp
  rfl
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
variable (t a : D.FacetUnit (A:=A) (D.bandCutParent q))

lemma surfaceWord_eval_raw (f : F) :
    (D.surfaceWord f).eval φ g =
      (List.ofFn fun k => (D.commutatorWord f k).eval φ g).prod *
      (List.ofFn fun b => (D.boundaryWord f b).eval φ g).prod := by
  simp only [surfaceWord,Term.eval,wordProduct_eval_raw,List.map_ofFn,Function.comp_def]

lemma bandCutLiftHandleProduct_parent :
    (List.ofFn fun k => ((D.bandCutDiagram q).commutatorWord (D.bandCutParent q) k).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a)).prod =
    t⁻¹*D.bandCutRetainedProduct q φ g (D.bandCutParent q)*t := by
  rw [bandCutLiftValues,bandCutHandleProduct_eval,bandCutHandleBase_parent,inv_inv]
  rfl

lemma bandCutLiftHandleProduct_other (f : F) (hf : f≠D.bandCutParent q) :
    (List.ofFn fun k => ((D.bandCutDiagram q).commutatorWord f k).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a)).prod =
    (List.ofFn fun k => (D.commutatorWord f k).eval φ g).prod := by
  rw [bandCutLiftValues,bandCutHandleProduct_eval,D.bandCutHandleBase_other q t f hf]
  simp only [one_mul,mul_one,inv_one]
  exact (D.bandCutOldHandleProduct_other q φ g f hf).symm

variable (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)
include hb

lemma bandCutLiftSurfaceRaw_parent :
    ((D.bandCutDiagram q).surfaceWord (D.bandCutParent q)).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) =
    t⁻¹*(D.bandCutRetainedProduct q φ g (D.bandCutParent q)*(t*a*t⁻¹*a⁻¹)*
      (List.ofFn fun b => (D.boundaryWord (D.bandCutParent q) b).eval φ g).prod)*t := by
  rw [surfaceWord_eval_raw,bandCutLiftHandleProduct_parent,
    D.bandCutBoundaryProduct_parent q φ g b0 i0 t a hb,
    D.bandCutOldBoundaryProduct_parent q φ g b0]
  let H : D.FacetUnit (A:=A) (D.bandCutParent q) :=
    D.bandCutRetainedProduct q φ g (D.bandCutParent q)
  let E : D.FacetUnit (A:=A) (D.bandCutParent q) := D.bandCutEarlier q φ g b0
  let L : D.FacetUnit (A:=A) (D.bandCutParent q) := D.bandCutLater q φ g b0
  let c : D.FacetUnit (A:=A) (D.bandCutParent q) := (D.boundaryWord (D.bandCutParent q) b0).eval φ g
  change (t⁻¹*H*t)*
      ((D.bandCutU q t a*E*(D.bandCutU q t a)⁻¹)*a*
        (D.bandCutV q φ g b0 t a*L*(D.bandCutV q φ g b0 t a)⁻¹)*
          (t⁻¹*a⁻¹*c*t)) = t⁻¹*(H*(t*a*t⁻¹*a⁻¹)*(E*c*L))*t
  simpa only [mul_assoc,bandCutU,bandCutV] using
    SurfaceSurgery.inverse_cut_ordered_word H E L c t a

lemma bandCutLiftSurface_other (f : F) (hf : f≠D.bandCutParent q) :
    ((D.bandCutDiagram q).surfaceWord f).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) = (D.surfaceWord f).eval φ g := by
  rw [surfaceWord_eval_raw,bandCutLiftHandleProduct_other,
    D.bandCutBoundaryProduct_other q φ g b0 i0 t a hb f hf,surfaceWord_eval_raw]
  · rfl
  · exact hf

variable (hg : 0 < D.genus (D.bandCutParent q))

lemma bandCutLiftSurface_parent :
    let t : D.FacetUnit (A:=A) (D.bandCutParent q) := g (.handle (D.bandCutParent q) (D.bandCutLastHandle q hg) false)
    let a : D.FacetUnit (A:=A) (D.bandCutParent q) := g (.handle (D.bandCutParent q) (D.bandCutLastHandle q hg) true)
    ((D.bandCutDiagram q).surfaceWord (D.bandCutParent q)).eval φ
      (D.bandCutLiftValues q φ g b0 i0 t a) =
    t⁻¹*(D.surfaceWord (D.bandCutParent q)).eval φ g*t := by
  dsimp only
  erw [D.bandCutLiftSurfaceRaw_parent q φ g b0 i0 _ _ hb,surfaceWord_eval_raw,
    D.bandCutOldHandleProduct_parent q φ g hg]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
variable (D : Diagram F S V arity) (q : S) (φ : R →+* A)
variable (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
variable (J T : D.BandCutUnit (A:=A) q)
variable (h : (f : F) → Fin ((D.bandCutDiagram q).genus f) → Bool → D.FacetUnit (A:=A) f)

lemma sameFramedFlag_unit_self {n : ℕ} (grade : Fin n → ℕ) (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    SameFramedFlag grade (matrixUnitEquiv u) (matrixUnitEquiv u) :=
  MatrixIso.holds_self grade (MatrixIso.unit u)

lemma bandCut_seamHolds
    (hs : ∀ s, SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g))) (s : BandCutSeam S) :
    SameFramedFlag ((D.bandCutDiagram q).seamGrade s)
      (matrixUnitEquiv (((D.bandCutDiagram q).seamLeft s).eval φ (D.bandCutValues q g J T h)))
      (matrixUnitEquiv (((D.bandCutDiagram q).seamRight s).eval φ (D.bandCutValues q g J T h))) := by
  rcases s with ⟨s,k⟩ | ⟨⟩
  · fin_cases k
    · erw [D.bandCut_seam_first q φ g J T h]
      exact sameFramedFlag_unit_self _ _
    · erw [D.bandCut_seam_middle q φ g J T h]
      exact sameFramedFlag_unit_self _ _
    · erw [(D.bandCut_seam_last q φ g J T h s).1,(D.bandCut_seam_last q φ g J T h s).2]
      exact hs s
  · erw [D.bandCut_seam_identity q φ g J T h]
    exact sameFramedFlag_unit_self _ _

lemma bandCut_vertexHolds (hv : D.VertexHolds g) :
    (D.bandCutDiagram q).VertexHolds (D.bandCutValues q g J T h) := by
  intro v
  rcases v with v | (⟨s,b⟩ | b)
  · rw [D.bandCut_vertexComparison_old q g J T h]
    exact hv v
  · exact D.bandCut_vertexComparison_continuation q g J T h s b
  · cases b
    · exact D.bandCut_vertexComparison_first q g J T h
    · exact D.bandCut_vertexComparison_last q g J T h
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence PortAssembly MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A] [Algebra R A]
variable (D : Diagram F S V arity) (q : S)
variable (hg : 0 < D.genus (D.bandCutParent q))
variable (P : D.Punctures R) (x : D.Solution P A)
variable (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
variable (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
variable (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)

abbrev bandCutHandleT : D.FacetUnit (A:=A) (D.bandCutParent q) :=
  x.val.val (.handle (D.bandCutParent q) (D.bandCutLastHandle q hg) false)
abbrev bandCutHandleA : D.FacetUnit (A:=A) (D.bandCutParent q) :=
  x.val.val (.handle (D.bandCutParent q) (D.bandCutLastHandle q hg) true)

def bandCutSolutionValues := D.bandCutLiftValues q (algebraMap R A) x.val.val b0 i0
  (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)

include hb
lemma bandCutSolutionSurface (f : F) :
    ((D.bandCutDiagram q).surfaceWord f).eval (algebraMap R A) (D.bandCutSolutionValues q hg P x b0 i0) =
    ((D.bandCutDiagram q).surfaceTarget (D.bandCutPunctures q P) f).eval (algebraMap R A)
      (D.bandCutSolutionValues q hg P x b0 i0) := by
  by_cases hf : f=D.bandCutParent q
  · subst f
    rw [bandCutSolutionValues, D.bandCutLiftSurface_parent q (algebraMap R A) x.val.val b0 i0 hb hg,
      D.actual_surface_relation P x,D.surfaceTarget_eval P x]
    change (D.bandCutHandleT q hg P x)⁻¹*scalarUnit _ (D.diskScalar P _)*(D.bandCutHandleT q hg P x)=_
    rw [(scalarUnit_commute (D.bandCutHandleT q hg P x)⁻¹ (D.diskScalar P _)).eq]
    erw [mul_assoc,inv_mul_cancel,mul_one]
    exact (map_scalarUnit _ _ _).symm
  · rw [bandCutSolutionValues,D.bandCutLiftSurface_other q (algebraMap R A) x.val.val b0 i0 _ _ hb f hf,
      D.actual_surface_relation P x]
    rfl

/-- Lift a solution over the coefficient algebra at a chosen parent occurrence. -/
def bandCutSolutionAt : (D.bandCutDiagram q).Solution (D.bandCutPunctures q P) A := by
  let t := D.bandCutHandleT q hg P x
  let a := D.bandCutHandleA q hg P x
  let G := D.bandCutLiftGauge q (algebraMap R A) x.val.val b0 t a
  let g' := D.gaugeGenerators G x.val.val
  let J := D.bandCutChosenJ q (algebraMap R A) g' b0 i0 a
  let T := D.bandCutChosenT q (algebraMap R A) g' b0 i0 t
  let h := D.bandCutRetainedHandles q g' t
  refine ⟨⟨D.bandCutSolutionValues q hg P x b0 i0,?_⟩,?_⟩
  · intro j
    rcases j with f | s
    · change SameFramedFlag (fun _ => 0)
        (matrixUnitEquiv (((D.bandCutDiagram q).surfaceWord f).eval (algebraMap R A) _))
        (matrixUnitEquiv (((D.bandCutDiagram q).surfaceTarget (D.bandCutPunctures q P) f).eval (algebraMap R A) _))
      rw [D.bandCutSolutionSurface q hg P x b0 i0 hb]
      exact sameFramedFlag_unit_self _ _
    · change SameFramedFlag ((D.bandCutDiagram q).seamGrade s)
        (matrixUnitEquiv (((D.bandCutDiagram q).seamLeft s).eval (algebraMap R A) (D.bandCutValues q g' J T h)))
        (matrixUnitEquiv (((D.bandCutDiagram q).seamRight s).eval (algebraMap R A) (D.bandCutValues q g' J T h)))
      apply D.bandCut_seamHolds q (algebraMap R A) g' J T h _ s
      intro s
      exact D.seamHolds_gauge (algebraMap R A) G x.val.val s (x.val.property (.inr s))
  · exact D.bandCut_vertexHolds q g' J T h (D.vertexHolds_gauge G x.val.val x.property)

omit hb in
/-- Choose an inverse nonseparating arc and preserve all vertex, boundary,
and surface equations over the coefficient algebra. -/
def inverseBandSolution : (D.bandCutDiagram q).Solution (D.bandCutPunctures q P) A := by
  let pos := D.boundarySide.symm (⟨q,none⟩ : Side S arity)
  have hpos : D.boundarySide pos=⟨q,none⟩ := D.boundarySide.apply_symm_apply _
  rcases pos with ⟨f,b,i⟩
  have hf : f=D.bandCutParent q := by
    have hh := D.boundaryFacet f b i
    rw [hpos] at hh
    exact hh.symm
  subst f
  exact D.bandCutSolutionAt q hg P x b i hpos
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
