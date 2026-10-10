import OAI.AlgebraicGeometry.CharacterVarieties.Seams.MarkedSurface
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames

namespace OAI

/-!
# A marked diagram from a field-valued solution

A solution of positive genus determines the band, marked diagram,
punctures, frames, and generator values for a nonseparating cut.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0<D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))

/-- The old generator coordinates after the necessary based-circle gauge. -/
def producedCutSeed := D.bandCutLiftGenerators q (algebraMap R K) x.val.val b0
  (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)

def producedCutJ := rebaseUnit (D.seamRank q).symm
  (D.bandCutChosenJ q (algebraMap R K) (D.producedCutSeed q hg P x b0) b0 i0
    (D.bandCutHandleA q hg P x))
def producedCutT := rebaseUnit (D.seamRank q).symm
  (D.bandCutChosenT q (algebraMap R K) (D.producedCutSeed q hg P x b0) b0 i0
    (D.bandCutHandleT q hg P x))

def producedCutBand := D.cutGeneratorWitness q (D.producedCutSeed q hg P x b0)
  (D.producedCutJ q hg P x b0 i0)

def producedMarkedDiagram := D.refinedMarkedDiagram q
  (D.producedCutBand q hg P x b0 i0).shape rfl
  (D.producedCutBand q hg P x b0 i0).rowRanks
  (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax

def producedMarkedFrames : (D.producedMarkedDiagram q hproper hmax hg P x b0 i0).PortFrames (R:=K) :=
  D.markedCutFrames q (D.producedCutBand q hg P x b0 i0) hproper hmax
    (D.portFrame (D.producedCutSeed q hg P x b0))
    (MatrixIso.unit (D.producedCutT q hg P x b0 i0))

def producedMarkedPunctures : (D.producedMarkedDiagram q hproper hmax hg P x b0 i0).Punctures R :=
  D.refinedMarkedPunctures q (D.producedCutBand q hg P x b0 i0).shape rfl
    (D.producedCutBand q hg P x b0 i0).rowRanks
    (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax P

def producedMarkedValues := D.refinedMarkedLiftValues q
  (D.producedCutBand q hg P x b0 i0).shape rfl
  (D.producedCutBand q hg P x b0 i0).rowRanks
  (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax (algebraMap R K) x.val.val
  b0 i0 (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)
  (D.producedMarkedFrames q hproper hmax hg P x b0 i0)

omit [Finite V] in
lemma producedCutSeed_vertexHolds : D.VertexHolds (D.producedCutSeed q hg P x b0) :=
  D.vertexHolds_gauge
    (D.bandCutLiftGauge q (algebraMap R K) x.val.val b0
      (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x)) x.val.val x.property

/-- The vertex equations of the produced marked diagram. -/
def ProducedMarkedVertexEquation : Prop :=
    (D.producedMarkedDiagram q hproper hmax hg P x b0 i0).VertexHolds
      (D.producedMarkedValues q hproper hmax hg P x b0 i0)

lemma producedMarkedValues_vertexHolds :
    D.ProducedMarkedVertexEquation q hproper hmax hg P x b0 i0 := by
  exact D.marked_values_vertexHolds q (D.producedCutBand q hg P x b0 i0) hproper hmax
    (D.portFrame (D.producedCutSeed q hg P x b0))
    (MatrixIso.unit (D.producedCutT q hg P x b0 i0))
    (D.producedCutSeed_vertexHolds q hg P x b0) _ _

/-- The surface equation of the produced marked diagram. -/
def ProducedMarkedSurfaceEquation
    (f : D.ports.RefinedBandFacet q (D.producedCutBand q hg P x b0 i0).shape) : Prop :=
    ((D.producedMarkedDiagram q hproper hmax hg P x b0 i0).surfaceWord f).eval (algebraMap R K)
      (D.producedMarkedValues q hproper hmax hg P x b0 i0)=
    ((D.producedMarkedDiagram q hproper hmax hg P x b0 i0).surfaceTarget
      (D.producedMarkedPunctures q hproper hmax hg P x b0 i0) f).eval (algebraMap R K)
      (D.producedMarkedValues q hproper hmax hg P x b0 i0)

lemma producedMarkedValues_surface
    (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩)
    (f : D.ports.RefinedBandFacet q (D.producedCutBand q hg P x b0 i0).shape) :
    D.ProducedMarkedSurfaceEquation q hproper hmax hg P x b0 i0 f :=
  D.refinedMarkedSolutionSurface q (D.producedCutBand q hg P x b0 i0).shape rfl
    (D.producedCutBand q hg P x b0 i0).rowRanks
    (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax b0 i0
    (D.producedMarkedFrames q hproper hmax hg P x b0 i0) hg P x hb f
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S)

lemma namedSeam_of_seamHolds
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (h : SameFramedFlag (D.seamGrade q)
      (matrixUnitEquiv ((D.seamLeft q).eval (algebraMap R K) g))
      (matrixUnitEquiv ((D.seamRight q).eval (algebraMap R K) g))) :
    SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
      ((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g))
      ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true)))) := by
  simp only [← MatrixIso.unit_linearEquiv] at h
  have z := MatrixIso.sameFramedFlag_reindex (D.seamGrade q) _ _
    (blockIndex (D.childDim q)).symm (finCongr (D.seamRank q)) h
  have he : (fun i => D.seamGrade q ((blockIndex (D.childDim q)).symm i))=
      (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val) := by
    funext i
    simp only [seamGrade,Equiv.apply_symm_apply]
  erw [he] at z
  change SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
    (D.namedSeamFrame q ((D.seamLeft q).eval (algebraMap R K) g))
    (D.namedSeamFrame q ((D.seamRight q).eval (algebraMap R K) g)) at z
  erw [D.namedSeamLeft,D.namedSeamRight] at z
  exact z

variable [Finite V]
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))

omit [Finite V] in
lemma producedCutSeed_namedSeam (s : S) :
    SameFramedFlag (fun i : (i : Fin (arity s)) × Fin (D.childDim s i) => i.1.val)
      ((D.namedSeamFrame s (D.producedCutSeed q hg P x b0 (.frame s false))).trans
        (D.namedParentLinear s (D.producedCutSeed q hg P x b0)))
      ((D.namedChildInverse s (D.producedCutSeed q hg P x b0)).trans
        (D.namedSeamFrame s (D.producedCutSeed q hg P x b0 (.frame s true)))) := by
  apply D.namedSeam_of_seamHolds (R:=R) s (D.producedCutSeed q hg P x b0)
  exact D.seamHolds_gauge (algebraMap R K)
    (D.bandCutLiftGauge q (algebraMap R K) x.val.val b0
      (D.bandCutHandleT q hg P x) (D.bandCutHandleA q hg P x))
    x.val.val s (x.val.property (.inr s))

omit [Finite V] in
lemma bandCutMirror_rebase
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (J T : D.BandCutUnit (A:=K) q) :
    rebaseUnit (D.seamRank q).symm (T⁻¹*J⁻¹*D.bandCutP q g*T)=
      (rebaseUnit (D.seamRank q).symm T)⁻¹ *
      (rebaseUnit (D.seamRank q).symm J)⁻¹ * (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
        (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) *
      rebaseUnit (D.seamRank q).symm T := by
  simp only [bandCutP]
  erw [map_mul, map_mul, map_mul, map_inv, map_inv, rebaseUnit_trans, rebaseUnit_refl]

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
