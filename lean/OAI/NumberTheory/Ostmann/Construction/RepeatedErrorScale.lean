import OAI.NumberTheory.Ostmann.Construction.RepeatedErrorScaleAbsorption
import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped FourierTransform SchwartzMap

theorem repeated_error_scale_eventually {Bs : ℝ} (hBs : 200≤Bs)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,
      ‖𝓕 SchwartzCutoff.psi 0‖ *
        Real.exp (-(Conclusion.initialGap Bs k L-(14+6*(k:ℝ)))/2) *
        (5000/L)^(2*Conclusion.bulkSize k L) * Real.exp (24*(Conclusion.bulkSize k L:ℝ)) *
        ((2*Conclusion.bulkSize k L+4*k+8:ℕ):ℝ)^(2*Conclusion.bulkSize k L+4*k+8) *
        Real.exp (2*L) ≤ (1/2)*Real.exp (-27*(Conclusion.bulkSize k L:ℝ)) :=
  RepeatedErrorScale.absorption_eventually (norm_nonneg _) hBs hk

end Ostmann.Construction

end

end OAI
