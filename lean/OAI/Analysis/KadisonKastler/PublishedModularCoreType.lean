import OAI.Analysis.KadisonKastler.RegularCoreAlgebra
import OAI.Analysis.KadisonKastler.ModularStateAction
import OAI.Analysis.KadisonKastler.SemifiniteFactor
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # The published factorial-core criterion

Takesaki, *Duality for crossed products and the structure of von Neumann
algebras of type III*, Acta Math. 131 (1973), Lemma 8.2 and Corollary 9.7,
identifies type III₁ by factoriality of the modular core. Blackadar,
*Operator Algebras*, III.4.8.1--4 (p.329), gives the semifinite core and
its independence of the faithful normal state. A semifinite factor has
core `M ⊗ L∞(ℝ)`, so the factorial-core criterion also excludes that case.

Only this consequence is retained. The modular action has a KMS
certificate; factoriality of the concrete core is a premise to be proved
by the application, never a field of a product-construction input.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Type III₁ expressed by the published continuous-core characterization.
The ordinary type III projection conditions are retained explicitly. -/
structure TypeIII1Factor (M : VonNeumannAlgebra H) : Prop extends TypeIIIFactor M where
  core_type : ∀ (Ω : H), ‖Ω‖ = 1 →
    DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
    ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
      (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)),
      (∀ t x, x ∈ M → unitaryConj (U t) x ∈ M) →
      IsModularStateGroup M Ω U → TypeIIInfinityFactor (regularCoreAlgebra U hU M)

/-- The factorial-core classification, specialized to a separably
represented factor and a faithful normal vector state. -/
def PublishedFactorialModularCore : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H],
    ∀ (M : VonNeumannAlgebra H), ScalarCenter M →
    ∀ (Ω : H), ‖Ω‖ = 1 →
      DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
    ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
      (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)),
      (∀ t x, x ∈ M → unitaryConj (U t) x ∈ M) → IsModularStateGroup M Ω U →
      ScalarCenter (regularCoreAlgebra U hU M) → TypeIII1Factor M

end

end KadisonKastler

end OAI
