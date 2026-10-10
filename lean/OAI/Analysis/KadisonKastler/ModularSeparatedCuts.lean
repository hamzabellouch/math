import OAI.Analysis.KadisonKastler.PublishedModularSpectral

namespace OAI

/-! # Separated modular cuts from the actual graph comparison -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cut comparison is proved from a one-algebra spectral resolution
and the independently proved two-algebra graph estimate. -/
theorem norm_modular_separated_cuts_le
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
    (J : H ≃ₗᵢ⋆[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hgraph : ∀ c : ℝ, 0 < c →
      ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ e)
    (a : ℝ) :
    ‖(1 - n.upperCut (a - 1 / 2)) * m.upperCut (a + 1 / 2)‖ ≤
      ((1 + Real.exp (-(1 / 2 : ℝ))) / (1 - Real.exp (-(1 / 2 : ℝ)))) * e := by
  obtain ⟨R, hR, hAR, hPR⟩ := m.high_inverse J a
  apply norm_logarithmically_separated_cuts_le
    (1 - graphResolvent M J Ω (Real.exp (-a / 2)))
    (1 - graphResolvent N J Ω (Real.exp (-a / 2)))
    (m.upperCut (a + 1 / 2)) (1 - n.upperCut (a - 1 / 2)) R he
    (n.lower_contracts _) hR (n.low_bound J a) ?_ hAR hPR (n.low_support J a)
  have hid : (1 - graphResolvent M J Ω (Real.exp (-a / 2))) -
      (1 - graphResolvent N J Ω (Real.exp (-a / 2))) =
      -(graphResolvent M J Ω (Real.exp (-a / 2)) -
        graphResolvent N J Ω (Real.exp (-a / 2))) := by abel
  rw [hid, norm_neg]
  exact (norm_graphResolvent_sub_le M N J Ω _).trans (hgraph _ (Real.exp_pos _))

end

end KadisonKastler

end OAI
