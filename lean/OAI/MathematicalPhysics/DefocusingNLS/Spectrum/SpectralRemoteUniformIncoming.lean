import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteOutgoingEstimate

namespace OAI

/-! Uniform incoming smallness on escaping half-lines. The decay exponent
and the reduction order are fixed before the parameter tends to infinity. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_uniform_incoming
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (C sigma : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hm : 1 ≤ m) (hgap : 5*C < 2*(m : ℝ))
    (hdecay : C+(sigma-2*(m : ℝ)) < 0)
    (c : ℕ → ℝ → Fin 2 → ℝ) (A R : ℕ → ℝ → SpectralRemoteOperator)
    (Y : ℕ → ℝ → SpectralRemoteSpace)
    (hc : HasUniformLogJetBound L 0 c) (hA : HasUniformLogJetBound L 0 A)
    (hR : HasUniformLogJetBound L (-2*(m : ℝ)) R)
    (hci : ∀ᶠ n in atTop, HasLogJetBound 0 (c n))
    (hAi : ∀ᶠ n in atTop, HasLogJetBound 0 (A n))
    (hRi : ∀ᶠ n in atTop, HasLogJetBound (-2*(m : ℝ)) (R n))
    (hYi : ∀ᶠ n in atTop, HasLogJetBound sigma (Y n))
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ k, |c n t k| ≤ 1/32)
    (hblock : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), spectralRemoteBlockOperator (A n t) = A n t)
    (hAb : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖A n t‖ ≤ C)
    (hAR : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖A n t+R n t‖ ≤ C)
    (hode : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      HasDerivAt (Y n) ((spectralRemoteLeadingOperator (c n t) t+A n t+R n t) (Y n t)) t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, ∀ T ∈ Ioi (L n),
      ‖spectralPhysicalDerivativeMap (Y n T)‖ ≤ K*Real.exp (-2*T)*‖Y n T‖ := by
  obtain ⟨D,hD,hDb⟩ := hR.bound 0
  let K := 2*D/(2*(m : ℝ)-5*C)
  have hK : 0 ≤ K := div_nonneg (by positivity) (sub_pos.mpr hgap).le
  refine ⟨K,hK,?_⟩
  filter_upwards [hc.smooth,hA.smooth,hR.smooth,hci,hAi,hRi,hYi,hsmall,hblock,hAb,hAR,hode,
    hDb,hL.eventually (eventually_ge_atTop (0 : ℝ))] with n hcs hAs hRs hcin hAin hRin
      hYin hcn hbn hAn hARn hYn hRn hLn
  intro T hT
  have hbR : ∀ t ∈ Ioi (L n), ‖R n t‖ ≤ D*Real.exp (-2*(m : ℝ)*t) := by
    simpa only [iteratedDeriv_zero] using hRn
  have hh := spectralRemote_outgoing_incoming_bound (L n) T C D sigma m hT hC hD
    hgap hdecay (c n) (A n) (R n) (Y n) hcin hAin hRin hYin
    hcs.continuousOn hAs.continuousOn hRs.continuousOn hcn hbn hAn hARn hbR hYn
  apply hh.trans
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have he : Real.exp (-2*(m : ℝ)*T) ≤ Real.exp (-2*T) :=
    Real.exp_le_exp.mpr (by nlinarith [hLn.trans hT.le])
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) (norm_nonneg _)

end DefocusingNLS

end OAI
