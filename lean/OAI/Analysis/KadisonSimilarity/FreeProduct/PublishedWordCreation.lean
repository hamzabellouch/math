import OAI.Analysis.KadisonSimilarity.Tracial.TracialCreationCoordinates
import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordModel
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialFreeCompression

namespace OAI

/-! The elementary creation part of the published reduced free-product model.

Ricard--Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2--3,
and Lemma 2.3: prepending a centered letter to a word from the opposite
factor is the Hilbert tensor insertion. This interface has only those raw
word maps; prefix isometry and propagation are derived separately. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

/-- Grouping ordinary reduced words by their first factor. Both the tail
space and the A-leading space are actual closed subspaces of the GNS space. -/
structure ReducedWordCreationModel where
  tail : ClosedSubmodule ℂ H
  head : TracialHeadCoordinates (G.baseGeometry D) G D.subtype tail
  aLead : ClosedSubmodule ℂ H
  createA : HilbertTensor (centeredSubspace (G.baseVector A 1)) head.vacuumᗮ →ₗᵢ[ℂ] H
  createD : HilbertTensor (centeredSubspace (G.baseVector D 1)) aLead →ₗᵢ[ℂ] H
  createA_mem : ∀ w, createA w ∈ aLead
  createD_mem : ∀ w, createD w ∈ head.vacuumᗮ
  actionA : ∀ (a : A) (ha : G.trace (a : P) = 0) (y : head.vacuumᗮ),
    G.left (a : P) y = createA (hilbertTensorInsert (G.baseSymmetryLetter A a ha) y)
  actionD : ∀ (d : D) (hd : G.trace (d : P) = 0) (y : aLead),
    G.left (d : P) y = createD (hilbertTensorInsert (G.baseSymmetryLetter D d hd) y)

/-- Published input specialized to the two actual tracial factors. -/
def RicardXuCreationInput : Prop :=
  G.trace 1 = 1 → Function.Injective G.vector → ScalarFree G.trace D A →
    ReducedWordGenerated G A D → Nonempty (ReducedWordCreationModel G A D)

namespace ReducedWordCreationModel

variable {G A D} (W : ReducedWordCreationModel G A D)

/-- The normalized Haar letters are among the centered algebra letters in
the published model, so the raw propagation formulas need no new hypothesis. -/
def tracialCreationFormulas
    (s : A) (hs : G.trace (s : P) = 0)
    {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
    (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a) :
    TracialCreationFormulas G A D W.head s hs z ha htrace hhaar W.aLead.toSubmodule where
  createA := W.createA
  createD := W.createD
  createA_mem := W.createA_mem
  createD_mem := W.createD_mem
  actionA := W.actionA s hs
  actionD n y := by
    have htraceD : (G.baseGeometry D).trace q = (a : ℂ) := by
      simpa only [G.baseGeometry_trace D] using htrace
    have hz := haarCornerLetter_trace_zero (G.baseGeometry D).trace z ha htraceD hhaar n
    exact W.actionD (haarCornerLetter z a n) hz y

end ReducedWordCreationModel

/-- The vacuum/creation coordinates for multiplication by the second factor.
The projection singles out words beginning in that factor, and `before` is
its orthogonal complement. No operator norm estimate is part of this data. -/
structure ReducedWordCompressionModel where
  tail : ClosedSubmodule ℂ H
  before : ClosedSubmodule ℂ H
  head : TracialHeadCoordinates (G.baseGeometry A) G A.subtype tail
  tailProjection : tail →L[ℂ] tail
  projection_adjoint : tailProjection.adjoint = tailProjection
  projection_sq : tailProjection * tailProjection = tailProjection
  projection_norm : ‖tailProjection‖ ≤ 1
  includeBefore : before →ₗᵢ[ℂ] HilbertTensor (G.baseSpace A) tail
  create : HilbertTensor (centeredSubspace (G.baseVector D 1)) before →ₗᵢ[ℂ]
    HilbertTensor (G.baseSpace A) tail
  complement : includeBefore.toContinuousLinearMap.comp includeBefore.toContinuousLinearMap.adjoint =
    1 - firstLetterProjection (G.baseVector A 1) tailProjection
  create_range : ∀ (b : D) (hb : G.trace (b : P) = 0) x,
    firstLetterProjection (G.baseVector A 1) tailProjection
      (create (hilbertTensorInsert (G.baseSymmetryLetter D b hb) x)) =
        create (hilbertTensorInsert (G.baseSymmetryLetter D b hb) x)
  create_word : ∀ (b : D) (hb : G.trace (b : P) = 0) x,
    head.unitary (G.left (b : P) (head.unitary.symm (includeBefore x))) =
      create (hilbertTensorInsert (G.baseSymmetryLetter D b hb) x)

/-- Section 1 and Lemma 2.3 of Ricard--Xu, restricted to one creation letter
and its preceding-word space in a scalar tracial reduced product. -/
def RicardXuCompressionInput : Prop :=
  G.trace 1 = 1 → Function.Injective G.vector → ScalarFree G.trace D A →
    ReducedWordGenerated G A D → Nonempty (ReducedWordCompressionModel G A D)

/-- The narrow-arc norm estimate follows from the published elementary
creation model and the proved three-block estimate. -/
theorem norm_narrow_compression_of_published_words
    (published : RicardXuCompressionInput G A D)
    (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)
    (hfree : ScalarFree G.trace D A) (hdense : ReducedWordGenerated G A D)
    (e : A) (he : IsStarProjection (e : P))
    (b : D) (hbself : star b = b) (hb0 : G.trace (b : P) = 0)
    {u : ℝ} (hu : 0 ≤ u) (hetrace : G.trace (e : P) = (u : ℂ))
    (hb₂ : (G.trace (star (b : P) * (b : P))).re ≤ u) (hbnorm : ‖(b : P)‖ ≤ 1) :
    ‖(e : P) * (b : P) * (e : P)‖ ≤ 3 * u := by
  obtain ⟨W⟩ := published hτ hfaithful hfree hdense
  exact G.norm_narrow_compression_of_reduced_words A D hfaithful hτ
    W.head.unitary W.head.left_head W.tailProjection W.projection_adjoint
    W.projection_sq W.projection_norm W.includeBefore W.create W.complement
    e he b hbself hb0 (W.create_range b hb0) (W.create_word b hb0) hu hetrace hb₂ hbnorm

end KadisonSimilarity

end

end OAI
