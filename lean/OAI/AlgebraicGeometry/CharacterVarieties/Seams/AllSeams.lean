import OAI.AlgebraicGeometry.CharacterVarieties.Seams.FirstShortSeam
import OAI.AlgebraicGeometry.CharacterVarieties.Seams.MarkedSeams
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.InheritedSeams
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.ShortSeams

namespace OAI

/-!
# Framed flags at every seam of a marked cut

The first, last, reflected, internal, and inherited seams satisfy their
framed flag equations.
-/

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

lemma allSeams_of_families (P : (wiring A q B).Seam → Prop)
    (hold : ∀ t,P (oldPort A q B t true))
    (horig : ∀ j,P (originalPort A q B j true))
    (hmirror : ∀ j,P (mirrorOutput A q B j))
    (hbranch : ∀ a,P (branchPlus A q B a))
    (hbranchNeg : ∀ a,P (branchNegPlus A q B a)) :
    ∀ s,P s := by
  intro s
  obtain ⟨z,rfl⟩ := (graftPlus A B.doublePatch).surjective s
  rcases z with t | (((j | j) | (a | a)) | b)
  · exact hold t
  · exact horig j.succ
  · exact hmirror j.castSucc
  · exact hbranch a
  · exact hbranchNeg a
  · cases b with
    | false => exact horig 0
    | true => exact hmirror (Fin.last B.length)


/-- The eight seam families exhaust the marked band graft. -/
lemma allSeams_of_eightFamilies (P : (wiring A q B).Seam → Prop)
    (hselected : P (oldPort A q B q true))
    (hinherited : ∀ s,s≠q → P (oldPort A q B s true))
    (hfirst : P (originalPort A q B 0 true))
    (horiginal : ∀ j : Fin B.length,P (originalPort A q B j.succ true))
    (hlastMirror : P (mirrorOutput A q B (Fin.last B.length)))
    (hmirror : ∀ j : Fin B.length,P (mirrorOutput A q B j.castSucc))
    (hpositive : ∀ a,P (branchPlus A q B a))
    (hnegative : ∀ a,P (branchNegPlus A q B a)) : ∀ s,P s := by
  have hold : ∀ s,P (oldPort A q B s true) := by
    intro s
    by_cases hs : s=q
    · subst s
      exact hselected
    · exact hinherited s hs
  have horig : ∀ j,P (originalPort A q B j true) :=
    fun j => Fin.cases hfirst horiginal j
  have hreflected : ∀ j,P (mirrorOutput A q B j) :=
    fun j => Fin.lastCases hlastMirror hmirror j
  exact allSeams_of_families A q B P hold horig hreflected hpositive hnegative


/-- A parameterized family of flags satisfies every seam equation if it satisfies each seam family. -/
lemma allSeams_of_eightFamilies_forall {H : Type} {Q : Prop}
    (P : H → (wiring A q B).Seam → Prop)
    (hselected : ∀ h,Q → P h (oldPort A q B q true))
    (hinherited : ∀ h,Q → ∀ s,s≠q → P h (oldPort A q B s true))
    (hfirst : ∀ h,P h (originalPort A q B 0 true))
    (horiginal : ∀ h (j : Fin B.length),P h (originalPort A q B j.succ true))
    (hlastMirror : ∀ h,P h (mirrorOutput A q B (Fin.last B.length)))
    (hmirror : ∀ h (j : Fin B.length),P h (mirrorOutput A q B j.castSucc))
    (hpositive : ∀ h a,P h (branchPlus A q B a))
    (hnegative : ∀ h a,P h (branchNegPlus A q B a)) : ∀ h,Q → ∀ s,P h s := by
  intro h hQ
  exact allSeams_of_eightFamilies A q B (P h) (hselected h hQ) (hinherited h hQ)
    (hfirst h) (horiginal h) (hlastMirror h) (hmirror h) (hpositive h) (hnegative h)

end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (w : IdentifiedBand (D.childDim q) (D.namedSeamFrame q (g (.frame q false)))
      (((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g)).trans
        (MatrixIso.unit J).linearEquiv.symm))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "FF" => D.markedCutFrames q w hproper hmax (D.portFrame g) T
private abbrev markedCutOriginalSideValues : D.SideValues (R:=K) :=
  fun a => g (.side a)
local notation "oldSides" => markedCutOriginalSideValues (D := D) (g := g)

private abbrev markedCutInnerTransport :
    (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ :=
  T.toUnit⁻¹*J⁻¹*(show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩))*T.toUnit
local notation "Y" => markedCutInnerTransport (D := D) (q := q) (g := g) (J := J) (T := T)
/-- The framed flag equation at a seam of a diagram. -/
def FramedSeamEquation (s : S) : Prop :=
  SameFramedFlag (D.seamGrade s)
    (matrixUnitEquiv ((D.seamLeft s).eval φ g))
    (matrixUnitEquiv ((D.seamRight s).eval φ g))

/-- The framed flag equation at a seam of the marked cut. -/
abbrev MarkedCutSeamFlag (handle : (C).HandleValues (R:=K))
    (s : (BandGraft.wiring (A) q (B)).Seam) : Prop :=
  let gg := valuesFromPorts (C) (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (oldSides) J (Y)) handle
  FramedSeamEquation (D := (C)) (g := gg) (φ := φ) s

/-- The selected old seam satisfies its framed flag equation. -/
def MarkedCutSelectedSeam : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)),
    (∀ s,SameFramedFlag (fun i : (i : Fin (arity s)) × Fin (D.childDim s i) => i.1.val)
      ((D.namedSeamFrame s (g (.frame s false))).trans (D.namedParentLinear s g))
      ((D.namedChildInverse s g).trans (D.namedSeamFrame s (g (.frame s true))))) →
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle (BandGraft.oldPort (A) q (B) q true)

lemma markedCut_selectedSeam : D.MarkedCutSelectedSeam q g J w T hproper hmax φ := by
  intro handle hold
  have out := D.markedLastShort_seamHolds q g J w T hproper hmax φ (Y) handle (hold q)
  exact out

/-- Inherited old seams satisfy their framed flag equations. -/
def MarkedCutInheritedSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)),
    (∀ s,SameFramedFlag (fun i : (i : Fin (arity s)) × Fin (D.childDim s i) => i.1.val)
      ((D.namedSeamFrame s (g (.frame s false))).trans (D.namedParentLinear s g))
      ((D.namedChildInverse s g).trans (D.namedSeamFrame s (g (.frame s true))))) →
    ∀ s : S,s≠q →
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle (BandGraft.oldPort (A) q (B) s true)

lemma markedCut_inheritedSeams : D.MarkedCutInheritedSeams q g J w T hproper hmax φ := by
  intro handle hold s hs
  have out := D.markedInherited_seamHolds q g w T hproper hmax φ J (Y) handle s hs (hold s)
  exact out

/-- The first marked original seam satisfies its framed flag equation. -/
def MarkedCutFirstSeam : Prop :=
  ∀ handle : (C).HandleValues (R:=K),
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle
      (BandGraft.originalPort (A) q (B) 0 true)

lemma markedCut_firstSeam : D.MarkedCutFirstSeam q g J w T hproper hmax φ := by
  intro handle
  have out := D.markedFirstShort_seamHolds q g w T hproper hmax φ (oldSides) J (Y) handle
  exact out

/-- The internal marked original seams satisfy their framed flag equations. -/
def MarkedCutOriginalInternalSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (k : Fin ((B).length)),
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle
      (BandGraft.originalPort (A) q (B) k.succ true)

lemma markedCut_originalInternalSeams :
    D.MarkedCutOriginalInternalSeams q g J w T hproper hmax φ := by
  intro handle k
  have out := D.markedOriginal_seamHolds q w (D.portFrame g) T hproper hmax φ
    (oldSides) J (Y) handle k
  exact out

/-- The last marked mirror seam satisfies its framed flag equation. -/
def MarkedCutLastMirrorSeam : Prop :=
  ∀ handle : (C).HandleValues (R:=K),
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle
      (BandGraft.mirrorOutput (A) q (B) (Fin.last (B).length))

lemma markedCut_lastMirrorSeam : D.MarkedCutLastMirrorSeam q g J w T hproper hmax φ := by
  intro handle
  have out := D.markedMirrorShort_seamHolds q g J w T hproper hmax φ handle
  exact out

/-- The internal marked mirror seams satisfy their framed flag equations. -/
def MarkedCutMirrorInternalSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (k : Fin ((B).length)),
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle
      (BandGraft.mirrorOutput (A) q (B) k.castSucc)

lemma markedCut_mirrorInternalSeams :
    D.MarkedCutMirrorInternalSeams q g J w T hproper hmax φ := by
  intro handle k
  have out := D.markedMirror_seamHolds q w (D.portFrame g) T hproper hmax φ
    (oldSides) J (Y) handle k
  exact out

/-- The positive seam family satisfies its framed flag equations. -/
def MarkedCutPositiveSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (a : BandGraft.PositiveBranch (A) q (B)),
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle (BandGraft.branchPlus (A) q (B) a)

lemma markedCut_positiveSeams : D.MarkedCutPositiveSeams q g J w T hproper hmax φ := by
  intro handle a
  have result := D.markedPositiveBranch_seamHolds q w (D.portFrame g) T hproper hmax φ
    (oldSides) J (Y) handle a
  exact result

/-- The negative seam family satisfies its framed flag equations. -/
def MarkedCutNegativeSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (a : BandGraft.NegativeBranch (A) q (B)),
    D.MarkedCutSeamFlag q g J w T hproper hmax φ handle (BandGraft.branchNegPlus (A) q (B) a)

lemma markedCut_negativeSeams : D.MarkedCutNegativeSeams q g J w T hproper hmax φ := by
  intro handle a
  have result := D.markedNegativeBranch_seamHolds q w (D.portFrame g) T hproper hmax φ
    (oldSides) J (Y) handle a
  exact result

/-- All seam equations of a marked cut follow from the original named seam flags. -/
def MarkedCutSeamEquations : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)),
    (∀ s,SameFramedFlag (fun i : (i : Fin (arity s)) × Fin (D.childDim s i) => i.1.val)
      ((D.namedSeamFrame s (g (.frame s false))).trans (D.namedParentLinear s g))
      ((D.namedChildInverse s g).trans (D.namedSeamFrame s (g (.frame s true))))) →
    ∀ s,D.MarkedCutSeamFlag q g J w T hproper hmax φ handle s

lemma markedCut_allSeams : D.MarkedCutSeamEquations q g J w T hproper hmax φ := by
  have out := BandGraft.allSeams_of_eightFamilies_forall (A) q (B)
    (D.MarkedCutSeamFlag q g J w T hproper hmax φ)
    (D.markedCut_selectedSeam q g J w T hproper hmax φ)
    (D.markedCut_inheritedSeams q g J w T hproper hmax φ)
    (D.markedCut_firstSeam q g J w T hproper hmax φ)
    (D.markedCut_originalInternalSeams q g J w T hproper hmax φ)
    (D.markedCut_lastMirrorSeam q g J w T hproper hmax φ)
    (D.markedCut_mirrorInternalSeams q g J w T hproper hmax φ)
    (D.markedCut_positiveSeams q g J w T hproper hmax φ)
    (D.markedCut_negativeSeams q g J w T hproper hmax φ)
  exact out
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
