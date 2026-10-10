import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteExteriorField
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteExteriorState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteODEJetGrowth

namespace OAI

/-! Coarse derivative growth and then all uniform logarithmic jets for the
actual canonical nonlinear exterior profile. No derivative bounds are assumed. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_exterior_uniform_growth
    (nu a : ℕ → ℂ) (nu0 a0 : ℂ) (hnu : Tendsto nu atTop (𝓝 nu0))
    (ha : Tendsto a atTop (𝓝 a0)) (delta L : ℝ) (hd : 0 < delta)
    (ha0 : ‖a0‖+2*delta < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (nu n) n (a n) L) :
    ∀ k : ℕ, ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t, T ≤ t → ‖iteratedDeriv k (fun s => (radialExteriorCanonical (nu n) n (a n) L s).1) t‖ ≤
        B*Real.exp (C*t) := by
  let Z := fun n => radialExteriorCanonical (nu n) n (a n) L
  obtain ⟨T,M,hT,hLT,hM,hb⟩ :=
    spectralRemote_exterior_state_bound nu a nu0 a0 hnu ha delta L hd ha0 hX
  have hode : ∀ᶠ n in atTop, ∀ t ∈ Ioi T,
      HasDerivAt (Z n) (radialExteriorODEField (nu n) n t (Z n t)) t := by
    filter_upwards [hX] with n hn
    intro t ht
    exact ((radialExteriorCanonical_spec hn).2.2 t (hLT.trans ht.le)).2
  have hsm : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Z n) (Ioi T) := by
    filter_upwards [hode] with n hn
    exact radialExteriorODE_solution_contDiffOn _ _ _ _ hn
  have hbase : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioi T, ‖Z n t‖ ≤ K :=
    ⟨M,by linarith,hb.mono (fun n hn t ht => (hn t ht.le).1)⟩
  have hfield := spectralRemote_exterior_field_jets nu nu0 hnu Z T (‖a0‖+delta) M hT
    (by positivity) (by linarith) hM (hb.mono (fun n hn t ht => hn t ht.le))
  have hg := spectralRemote_ode_jet_growth T
    (fun n => Function.uncurry (radialExteriorODEField (nu n) n)) Z
    (fun n => radialExteriorODEField_contDiff _ _) hsm hode hbase hfield
  intro k
  obtain ⟨C,D,hC,hD,hgk⟩ := hg k
  refine ⟨C,D,max T 0+1,hC,by linarith,?_⟩
  filter_upwards [hgk,hsm] with n hn hsn
  intro t ht
  have hTt : T < t := lt_of_le_of_lt (le_max_left _ _) (by linarith : max T 0 < t)
  have hh := (ContinuousLinearMap.fst ℝ ℂ ℂ).norm_iteratedFDeriv_comp_left (x := t)
    ((hsn t hTt).contDiffAt (Ioi_mem_nhds hTt)) (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    ContinuousLinearMap.norm_fst,one_mul] at hh
  exact hh.trans (hn t (by change max T 0 < t; linarith) k le_rfl)

theorem spectralRemote_exterior_uniform_symbol
    (nu a : ℕ → ℂ) (nu0 a0 : ℂ) (hnu : Tendsto nu atTop (𝓝 nu0))
    (ha : Tendsto a atTop (𝓝 a0)) (delta L : ℝ) (hd : 0 < delta)
    (ha0 : ‖a0‖+2*delta < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (nu n) n (a n) L)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop) :
    HasUniformLogJetBound S 0 (fun n t => (radialExteriorCanonical (nu n) n (a n) L t).1) :=
  spectralRemote_exterior_symbol nu a nu0 a0 hnu ha delta L hd ha0 hX S hS
    (spectralRemote_exterior_uniform_growth nu a nu0 a0 hnu ha delta L hd ha0 hX)

end DefocusingNLS

end OAI
