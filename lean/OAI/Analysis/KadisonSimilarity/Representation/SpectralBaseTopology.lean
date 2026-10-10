import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Module.WeakDual

namespace OAI

/-! The spectrum of a norm-separable commutative C-star algebra is a
compact metrizable base for its vector spectral measures. -/

noncomputable section
namespace KadisonSimilarity

variable (A : Type*) [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]

theorem characterSpace_metrizable :
    TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) := by
  apply WeakDual.metrizable_of_isCompact ℂ A
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem characterSpace_secondCountable :
    SecondCountableTopology (WeakDual.characterSpace ℂ A) := by
  let : TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) :=
    characterSpace_metrizable A
  infer_instance

end KadisonSimilarity

end

end OAI
