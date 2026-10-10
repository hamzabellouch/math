import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundarySystem

namespace OAI

/-! Enlarging a Green constant preserves the constructed boundary system. -/

open Set
namespace DefocusingNLS

noncomputable def SpectralScalarBoundarySystem.withBound {R E A : ℝ}
    (S : SpectralScalarBoundarySystem R E A) (B : ℝ) (hAB : A ≤ B) :
    SpectralScalarBoundarySystem R E B :=
  { S with
    green := fun r hr t ht => (S.green r hr t ht).trans
      (div_le_div_of_nonneg_right hAB (S.positive_k t ht).le) }

end DefocusingNLS

end OAI
