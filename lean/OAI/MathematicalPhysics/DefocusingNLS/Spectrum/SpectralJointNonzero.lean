import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMovingParameterLimit

namespace OAI

/-! Joint convergence preserves nonvanishing on one fixed parameter neighborhood. -/

open Filter Topology Set
namespace DefocusingNLS

theorem spectral_joint_nonzero_neighborhood (F : ℕ → ℂ → ℂ) (z v : ℂ)
    (hv : v ≠ 0)
    (hF : Tendsto (fun p : ℕ × ℂ => F p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 v)) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∀ᶠ n in atTop, ∀ w ∈ U, F n w ≠ 0 := by
  have he := hF.eventually (eventually_ne_nhds hv)
  obtain ⟨A,hA,B,hB,hAB⟩ := Filter.mem_prod_iff.mp he
  obtain ⟨U,hUB,hU,hz⟩ := mem_nhds_iff.mp hB
  refine ⟨U,hU,hz,?_⟩
  filter_upwards [hA] with n hn w hw
  exact hAB (show (n,w) ∈ A ×ˢ B from ⟨hn,hUB hw⟩)

end DefocusingNLS

end OAI
