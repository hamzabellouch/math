import OAI.Analysis.KadisonKastler.PublishedTypeIIIProjection
import OAI.Analysis.KadisonKastler.Amenable

namespace OAI

/-! # The published injectivity input for type I factors

Blackadar, *Operator Algebras* (Springer, 2006), Corollary IV.2.2.10,
states that every type I von Neumann algebra is injective. Proposition
IV.2.1.4(iii) expresses this by a contractive projection in every faithful
representation. We retain only the factor case in its given representation.

The projection-theoretic hypothesis below is the usual characterization:
a factor is type I precisely when it has a nonzero minimal projection.
See III.1.3.10 and III.1.5.2--3. The latter also give the familiar spatial
form `B(H₁) ⊗ 1`. No perturbation or stability assertion is assumed.

Primary author PDF: https://bruceblackadar.com/Mathematics/Cycr.pdf
(printed pp. 244, 247, 373, 377).
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A nonzero projection with no proper nonzero subprojection in the
algebra. The order is the existing order on algebra projections. -/
def IsMinimalProjectionIn (M : VonNeumannAlgebra H) (p : AlgebraProjection M) : Prop :=
  p.val ≠ 0 ∧ ∀ q : AlgebraProjection M, q ≤ p → q.val = 0 ∨ q = p

/-- A type I factor, expressed only in terms of its scalar center and
the existence of a minimal projection. -/
structure IsTypeIFactor (M : VonNeumannAlgebra H) : Prop where
  factor : ScalarCenter M
  minimal : ∃ p : AlgebraProjection M, IsMinimalProjectionIn M p

/-- The factor specialization of Blackadar IV.2.2.10. -/
def PublishedTypeIInjectivity : Prop :=
  ∀ M : VonNeumannAlgebra H, IsTypeIFactor M → IsInjective M

end KadisonKastler

end OAI
