import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteExteriorJets
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonicalLimit

namespace OAI

/-! Uniform profile symbols remain valid for arbitrary cofinal powers and
independently chosen escaping endpoints. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_exterior_subsequence_symbol
    (s : ℕ → ℕ) (hs : StrictMono s) (nu a : ℕ → ℂ) (q0 a0 : ℂ)
    (hq0 : -1 < q0.re) (hnu : Tendsto nu atTop (𝓝 (-2*q0)))
    (ha : Tendsto a atTop (𝓝 a0)) (delta rho L : ℝ)
    (hd : 0 < delta) (hdm : delta < ‖a0‖) (ha0 : ‖a0‖+2*delta < 1) (hrho : rho < 1)
    (hupper : ∀ t, L ≤ t → ‖(radialFreeSlowJet q0 a0 t).1‖+2*delta ≤ rho)
    (hlower : ∀ t, L ≤ t → delta < ‖(radialFreeSlowJet q0 a0 t).1‖)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop) :
    HasUniformLogJetBound S 0 (fun i t => (radialExteriorCanonical (nu i) (s i) (a i) L t).1) ∧
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ i in atTop, ∀ t ∈ Ioi (S i),
      ‖(radialExteriorCanonical (nu i) (s i) (a i) L t).1‖ ≤ r := by
  let nuE := radialParameterExtension s nu (-2*q0)
  let aE := radialParameterExtension s a a0
  have hnuE := radialParameterExtension_tendsto s hs nu (-2*q0) hnu
  have haE := radialParameterExtension_tendsto s hs a a0 ha
  have hXE : ∀ᶠ n in atTop, HasRadialExterior (nuE n) n (aE n) L :=
    (radialExteriorCanonical_H_limit nuE aE q0 a0 hq0 hnuE haE delta rho L
      hd hdm ha0 hrho hupper hlower).1
  have hX : ∀ᶠ i in atTop, HasRadialExterior (nu i) (s i) (a i) L := by
    simpa only [nuE,aE,radialParameterExtension_apply s hs] using hs.tendsto_atTop.eventually hXE
  constructor
  · refine ⟨?_,?_⟩
    · filter_upwards [hX,hS.eventually (eventually_ge_atTop L)] with i hi hSi
      exact (radialExteriorODE_position_contDiffOn _ _ _ L
        (fun t ht => ((radialExteriorCanonical_spec hi).2.2 t ht.le).2)).mono (Ioi_subset_Ioi hSi)
    · intro k
      obtain ⟨B,T,hB,hb⟩ := spectralRemote_exterior_eventual_jets nuE aE (-2*q0) a0 hnuE haE
        delta L hd ha0 hXE k
      have hbi : ∀ᶠ i in atTop, ∀ t, T ≤ t →
          ‖iteratedDeriv k (fun u => (radialExteriorCanonical (nu i) (s i) (a i) L u).1) t‖ ≤ B := by
        simpa only [nuE,aE,radialParameterExtension_apply s hs] using hs.tendsto_atTop.eventually hb
      refine ⟨B,hB,?_⟩
      filter_upwards [hbi,hS.eventually (eventually_ge_atTop T)] with i hi hSi
      intro t ht
      simpa only [zero_mul,Real.exp_zero,mul_one] using hi t (hSi.trans ht.le)
  · obtain ⟨T,M,_,_,_,hb⟩ := spectralRemote_exterior_state_bound nuE aE (-2*q0) a0 hnuE haE
      delta L hd ha0 hXE
    refine ⟨‖a0‖+delta,by positivity,by linarith,?_⟩
    have hbi : ∀ᶠ i in atTop, ∀ t, T ≤ t →
        ‖(radialExteriorCanonical (nu i) (s i) (a i) L t).1‖ ≤ ‖a0‖+delta := by
      have hb' := hs.tendsto_atTop.eventually hb
      simpa only [nuE,aE,radialParameterExtension_apply s hs] using
        hb'.mono (fun i hi t ht => (hi t ht).2)
    filter_upwards [hbi,hS.eventually (eventually_ge_atTop T)] with i hi hSi
    intro t ht
    exact hi t (hSi.trans ht.le)

end DefocusingNLS

end OAI
