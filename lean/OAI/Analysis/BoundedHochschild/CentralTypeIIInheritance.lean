import OAI.Analysis.BoundedHochschild.CornerEquivalences
import OAI.Analysis.BoundedHochschild.FiniteCentralDecomposition

namespace OAI

/-!
# Type II inheritance by central corners

An abelian subcorner remains abelian in the ambient algebra. Consequently the
type I condition on a corner lifts to its ambient projection, and absence of a
type I central part passes to central corners. No trace is used.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
/-- Abelianness of a projection in a corner is its ambient abelianness. -/
lemma abelianProjection_corner_to_ambient {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q)
    (hab : PopaTypeII.AbelianProjection hq) :
    PopaTypeII.AbelianProjection (corner_projection_coe p hp hq) := by
  let lift (a : PopaCorner.algebra (corner_projection_coe p hp hq)) :
      PopaCorner.algebra hq :=
    ⟨⟨(a : M), by
      constructor
      · calc
          p * (a : M) = p * ((q : M) * (a : M)) := by rw [a.property.1]
          _ = (a : M) := by rw [← mul_assoc, q.property.1, a.property.1]
      · calc
          (a : M) * p = ((a : M) * (q : M)) * p := by rw [a.property.2]
          _ = (a : M) := by rw [mul_assoc, q.property.2, a.property.2]⟩,
      Subtype.ext a.property.1, Subtype.ext a.property.2⟩
  intro a b
  apply Subtype.ext
  exact congrArg (fun t : PopaCorner.algebra hq => ((t : Corner p hp) : M))
    (hab (lift a) (lift b)).eq

/-- A type I corner of a corner is type I at its ambient projection. -/
lemma typeICorner_corner_to_ambient {p : M} (hp : IsStarProjection p)
    (z : Corner p hp) (hz : IsStarProjection z)
    (hI : PopaTypeII.TypeICorner hz) :
    PopaTypeII.TypeICorner (corner_projection_coe p hp hz) := by
  intro r hr hrz hr0
  have hrp : r ≤ p := hrz.trans (corner_projection_le p hp hz)
  let rC : Corner p hp := ⟨r, projection_mem_corner hp hr hrp⟩
  have hrC : IsStarProjection rC :=
    ⟨Subtype.ext hr.isIdempotentElem.eq, Subtype.ext hr.isSelfAdjoint.star_eq⟩
  have hrCz : rC ≤ z := hrz
  have hrC0 : rC ≠ 0 := fun h => hr0 (congrArg Subtype.val h)
  obtain ⟨q, hq, hqr, hq0, hqa⟩ := hI rC hrC hrCz hrC0
  refine ⟨(q : M), corner_projection_coe p hp hq, hqr, ?_,
    abelianProjection_corner_to_ambient hp q hq hqa⟩
  exact fun h => hq0 (Subtype.ext h)

/-- The absence of a type I central part passes to a central corner. -/
theorem noTypeICentralPart_centralCorner {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p)
    (hM : PopaTypeII.NoTypeICentralPart M) :
    PopaTypeII.NoTypeICentralPart (Corner p hp) := by
  intro z hz hzc hz0 hI
  apply hM (z : M) (corner_projection_coe p hp hz)
  · intro a
    exact centralCorner_central hp hc z (fun b => (hzc b).eq) a
  · exact fun h => hz0 (Subtype.ext h)
  · exact typeICorner_corner_to_ambient hp z hz hI

/-- A smaller ambient central corner inherits the type II condition from a
larger corner. Centrality of the larger projection is not needed. -/
theorem noTypeICentralPart_smaller_centralCorner {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q)
    (hcp : ∀ a : M, p * a = a * p)
    (hQ : PopaTypeII.NoTypeICentralPart (Corner q hq)) :
    PopaTypeII.NoTypeICentralPart (Corner p hp) := by
  let pQ : Corner q hq := ⟨p, projection_mem_corner hq hp hpq⟩
  have hpQ : IsStarProjection pQ :=
    ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩
  have hpc : ∀ a : Corner q hq, pQ * a = a * pQ := by
    intro a
    exact Subtype.ext (hcp (a : M))
  exact noTypeICentralPart_map_equiv (nestedCornerEquiv hq pQ hpQ)
    (noTypeICentralPart_centralCorner hpQ hpc hQ)

/-- Central-corner inheritance with both ambient centrality witnesses. -/
theorem noTypeICentralPart_centralCorner_mono {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hcp : ∀ a : M, p * a = a * p) (_hcq : ∀ a : M, q * a = a * q)
    (hpq : p ≤ q) (hQ : PopaTypeII.NoTypeICentralPart (Corner q hq)) :
    PopaTypeII.NoTypeICentralPart (Corner p hp) :=
  noTypeICentralPart_smaller_centralCorner hp hq hpq hcp hQ

end KadisonRingrose
end BoundedHochschild

end

end OAI
