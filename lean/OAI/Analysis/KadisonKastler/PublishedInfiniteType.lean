import OAI.Analysis.KadisonKastler.PublishedProperInfiniteProjection

namespace OAI

/-! # Infinite identities in factors

Blackadar, *Operator Algebras*, III.1.3.4--5 (pp.242--243), proves that
an infinite projection has a nonzero properly infinite central part.
In a factor the central part is the identity. Only the resulting pair
of orthogonal isometries is retained here.
-/

namespace KadisonKastler

universe u

def PublishedInfiniteFactorProperlyInfinite : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H), ScalarCenter M →
      ¬ FiniteProjectionIn M 1 → ProperlyInfiniteIdentity M

end KadisonKastler

end OAI
