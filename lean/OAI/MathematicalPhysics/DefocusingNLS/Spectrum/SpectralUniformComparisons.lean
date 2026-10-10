import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningUniformSystems
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnUniformBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnUniformSlope
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnComparison

namespace OAI

/-! The actual scalar comparisons have common constants for every inner
endpoint in a fixed shell. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_uniform_comparisons
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R B : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hRB : R ≤ B) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : SpectralTurningFamilyData ell h b omega gamma r₀ d E) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ), StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧
      ∀ᶠ n in atTop, ∀ L ∈ Icc R B,
      ∃ S : SpectralScalarBoundarySystem L (E (φ n)) K,
        SpectralTurningComparison S J h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) (d (φ n)) :=
  spectralTurning_uniform_inward_systems ell h b omega gamma r₀ d E R B hh hR hRB hr₀ hdata

theorem spectralNoTurn_uniform_comparisons
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ (K J : ℝ) (eps : ℕ → ℝ), 0 ≤ K ∧ 0 ≤ J ∧
      (∀ n, 0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ L ∈ Icc R B,
      ∃ S : SpectralScalarBoundarySystem L (E n) K,
        SpectralNoTurnComparison S J (eps n) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) := by
  obtain ⟨K,J,hK,hJ,hsys⟩ := spectralNoTurn_uniform_boundary_systems
    ell b omega gamma E C R B hC hR hRB hCR hw hdata
  have hslope := spectralNoTurn_eventual_uniform_slope ell b omega gamma E C R B hC hR hRB hCR hw hdata
  have hE := (spectralNoTurn_eventual_data ell b omega gamma E C R hC hR hw hdata).1
  let eps := fun n => max 0 (spectralNoTurnRealError C R (omega n) (E n))
  have heps : Tendsto eps atTop (𝓝 0) := by
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have ht := hzero.max (spectralNoTurn_real_error_tendsto omega E C R hw hE)
    simpa only [max_self] using ht
  refine ⟨K,J,eps,hK,hJ,fun _ => le_max_left _ _,heps,?_⟩
  filter_upwards [hsys,hslope] with n hn hsn
  intro L hL
  obtain ⟨S,hk,hV,hbeta,hUE,hext⟩ := hn L hL
  refine ⟨S,hk,hV,hbeta,hext,?_⟩
  have hh := hsn L hL S.U S.continuous_U hUE (fun t ht => by
    simpa only [hV] using S.ode_U t ⟨ht.1.le,ht.2.le⟩)
  exact hh.2.trans (le_max_right _ _)

end DefocusingNLS

end OAI
