import OAI.CategoryTheory.Thomason.Simplicial.AcyclicKanSimplexLifting
import OAI.CategoryTheory.Thomason.Transfer.ThomasonLeftProperness

namespace OAI

section

/-! # Transport of attachment stability to the literal Thomason generators -/

namespace Thomason.Construction

open CategoryTheory PartialOrder StrictOmegaCategory CobaseChangeCellularClosure
open scoped Simplicial

noncomputable section

namespace DoubleSubdivisionPairs

/-- Every property respecting arrow isomorphisms sees the literal twice
subdivided inclusion as the finite old-chain inclusion. -/
theorem map_property_iff {C : Type*} [Category* C] (F : SSet.{0} ⥤ C)
    (W : MorphismProperty C) [W.RespectsIso]
    {m : ℕ} (A : (Δ[m] : SSet.{0}).Subcomplex) :
    W (F.map (SSet.sd.map (SSet.sd.map A.ι))) ↔
      W (F.map (nerveMap (subposetInclusion (ChainSieve.old (oldFaces A))).monotone.functor)) := by
  let e : Arrow.mk (SSet.sd.map (SSet.sd.map A.ι)) ≅
      Arrow.mk (nerveMap (subposetInclusion (ChainSieve.old (oldFaces A))).monotone.functor) :=
    Arrow.isoMk (sourceIso A) (targetIso m) (inclusion A)
  exact W.arrow_mk_iso_iff (F.mapArrow.mapIso e)

end DoubleSubdivisionPairs

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The actual twice-subdivided inclusion of any simplex subcomplex
universally preserves Street weak equivalences under attachment. -/
theorem subcomplex_attachment_universal
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {m : ℕ} (A : (Δ[m] : SSet.{0}).Subcomplex) :
    universalWeakPreserving h.streetWeakEquivalences (h.thomasonLeft.map A.ι) := by
  let : Finite (DoubleSubdivisionPairs.Faces m) := finite_nonemptyFiniteChains _
  change universalWeakPreserving h.streetWeakEquivalences
    (h.categorification.map (SSet.sd.map (SSet.sd.map A.ι)))
  apply (DoubleSubdivisionPairs.map_property_iff h.categorification
    (universalWeakPreserving h.streetWeakEquivalences) A).mpr
  exact h.finite_chain_attachment_universal G aw s g kq (DoubleSubdivisionPairs.oldFaces A)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The same literal-generator transport in every positive finite dimension. -/
theorem subcomplex_attachment_universal
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {m : ℕ} (A : (Δ[m] : SSet.{0}).Subcomplex) :
    universalWeakPreserving (thomasonWeakEquivalences (n := n) h)
      ((r.thomasonLeft h).map A.ι) := by
  let : Finite (DoubleSubdivisionPairs.Faces m) := finite_nonemptyFiniteChains _
  change universalWeakPreserving (thomasonWeakEquivalences (n := n) h)
    ((r.categorification h).map (SSet.sd.map (SSet.sd.map A.ι)))
  apply (DoubleSubdivisionPairs.map_property_iff (r.categorification h)
    (universalWeakPreserving (thomasonWeakEquivalences (n := n) h)) A).mpr
  exact r.finite_chain_attachment_universal h G t aw s g kq (DoubleSubdivisionPairs.oldFaces A)

end FiniteReflectionInput

end

end Thomason.Construction

end

end OAI
