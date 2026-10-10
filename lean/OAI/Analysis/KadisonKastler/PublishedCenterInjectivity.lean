import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.KadisonKastler.Amenable

namespace OAI

/-! # Published injectivity of the concrete center

Blackadar, *Operator Algebras*, Corollary IV.2.2.10, p. 377 (PDF p. 385),
states that commutative von Neumann algebras are injective. Proposition
IV.2.1.4(iii), p. 373, gives the norm-one projection in every faithful
representation. Only centers in their given representation are retained.

Primary text: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The represented-center specialization; no perturbation conclusion is assumed. -/
def PublishedCenterInjectivity : Prop :=
  ∀ M : VonNeumannAlgebra H, IsInjective (concreteCenter M)

end KadisonKastler

end OAI
