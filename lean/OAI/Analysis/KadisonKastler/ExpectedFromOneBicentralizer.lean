import OAI.Analysis.KadisonKastler.BicentralizerScalarStateTransport
import OAI.Analysis.KadisonKastler.ExpectedFromBicentralizer

namespace OAI

/-! # The expected matrix subfactor needs one scalar bicentralizer

Faithful-state homogeneity transports scalarity to the other states used
in the finite-matrix refinement. The chosen reference state is arbitrary.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance expectedOneBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem expectedMatrixSubfactorModel_of_one_bicentralizer
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hcyc : DenseRange (algebraVectorMap M ξ)) (d : ModularConjugationData M ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic d.conjugation a ξ))
    (hhom : FaithfulVectorStateHomogeneity M)
    (hscalar : ∀ a : Algebra M, stateBicentralizerMember ξ a → ∃ z : ℂ, a=z • 1) :
    Nonempty (ExpectedMatrixSubfactorModel M) :=
  expectedMatrixSubfactorModel_of_bicentralizer hM ξ hunit hsep hcyc d hpos hhom
    (hhom.scalar_bicentralizers_of_one ξ hunit hsep hscalar)

end

end KadisonKastler

end OAI
