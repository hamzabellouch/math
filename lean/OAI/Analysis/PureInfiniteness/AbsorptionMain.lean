import OAI.Analysis.PureInfiniteness.AbsorptionCanonicalTensor
import OAI.Analysis.OInfinity.ConnectedHalfFlipTheorem

namespace OAI

/-! Corollary 1.3: every separable nuclear weakly purely infinite C*-algebra
absorbs O∞, without unitality or simplicity hypotheses. The fixed integer
amplification condition is exactly that of the manuscript. -/

noncomputable section
namespace WeakPureInfiniteness.Campaign

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem nuclear_absorption
    (hA : Nuclear A) {n : ℕ} (hn : 1 ≤ n) (hF : FixedAmplification A n) :
    AbsorbsOInfinity A :=
  nuclear_absorption_of_canonical_halfFlip hA
    (oInfinity_connectedHalfFlip (minimalHalfFlipTensorModel OInfinity).map) hn hF

theorem nuclear_weaklyPurelyInfinite_absorption
    (hA : Nuclear A) (hW : WeaklyPurelyInfinite A) : AbsorbsOInfinity A := by
  obtain ⟨n, hn, hF⟩ := weaklyPurelyInfinite_iff.mp hW
  exact nuclear_absorption hA hn hF

end WeakPureInfiniteness.Campaign

end

end OAI
