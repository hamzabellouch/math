import Mathlib
import OAI.Analysis.CoulombIonization.Variational.IntegratedLipschitzControl
import OAI.Analysis.CoulombIonization.FieldAnalysis.SmearTestRecovery
import OAI.Analysis.CoulombIonization.Localization.ConditionalSandwich
import OAI.Analysis.CoulombIonization.Variational.MasterRecovery

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshPosteriorSandwich_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

open CoulombObservation CoulombNeumann CoulombAnalysis

theorem fresh_original_posterior_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ (c : Fin N → Fin 2),
      (spatialProduct (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) c).value z.1 ≠ 0 →
      ∀ s : Spins (cutOutNumber c),
      let u := cutOutPositions c z.1
      let S := radialPatchRetention N y t b c s u
      ‖(∫ v, g v*retainedSmear b S u v)-posteriorTestValue μ ell j g z‖ ≤
        ((S.filter (fun i => ‖u i-y‖ ≤ r+Real.sqrt 3*b)).card:ℝ)*
          ((L:ℝ)*(Real.sqrt 3*b))+
        2*observedLocalCount ell k y (r+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k)) := by
  filter_upwards [raw_posterior_local_test_error μ ell hell k hk hg y r hs] with z hz
  intro c hc s
  dsimp only
  have hm := radialCut_local_smear_error y ht hb hr c z.1 hc s hg hs
  have he : (∫ v, g v*retainedSmear b
      (radialPatchRetention N y t b c s (cutOutPositions c z.1)) (cutOutPositions c z.1) v)-
        posteriorTestValue μ ell j g z =
      ((∫ v, g v*retainedSmear b
        (radialPatchRetention N y t b c s (cutOutPositions c z.1)) (cutOutPositions c z.1) v)-
          (∑ i, g (z.1 i)))+((∑ i, g (z.1 i))-posteriorTestValue μ ell j g z) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hm (by simpa only [Real.norm_eq_abs] using hz))

end Work_FreshPosteriorSandwich_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal ContDiff

open CoulombObservation CoulombNeumann CoulombAnalysis

def masterPosterior {N K : ℕ} (μ : Measure (Configuration N)) (ell : Fin K → ℝ)
    (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) (y : Space) : ℝ :=
  posteriorTestValue μ ell j (fun x => masterKernel c₁ r₀ s g x y) z

theorem master_fresh_original_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    {c₁ r₀ d : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hd : 0 < d) (hd1 : d ≤ 1)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hretain : 2*masterWidth c₁ r₀ d y < t-7*b) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ (c : Fin N → Fin 2),
      (spatialProduct (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) c).value z.1 ≠ 0 →
      ∀ spin : Spins (cutOutNumber c),
      let u := cutOutPositions c z.1
      let S := radialPatchRetention N y t b c spin u
      ‖(∫ v, masterKernel c₁ r₀ d g v y*retainedSmear b S u v)-
          masterPosterior μ ell j c₁ r₀ d g z y‖ ≤
        ((S.filter (fun i => ‖u i-y‖ ≤ 2*masterWidth c₁ r₀ d y+Real.sqrt 3*b)).card:ℝ)*
          (((masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ d y)⁻¹^4)*(Real.sqrt 3*b))+
        2*observedLocalCount ell k y (2*masterWidth c₁ r₀ d y+Real.sqrt 3*ell k) z*
          (((masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ d y)⁻¹^4)*(Real.sqrt 3*ell k)) := by
  exact fresh_original_posterior_sandwich μ ell hell k hk y ht hb hretain
    (masterKernel_test_lipschitz hg hgs hc hcL hr hd hd1 y)
    (masterKernel_test_support hg hgs hc hcL hr hd hd1 y)

theorem master_radial_patch_recovery {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {c₁ r₀ d : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hd : 0 < d) (hd1 : d ≤ 1)
    (hR : 4*masterWidth c₁ r₀ d y < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ spin : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestSquare (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) spin Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c spin) (masterCenteredKernel c₁ r₀ d g y) u) ≤
      (128*(masterTestConstant hg hgs:ℝ)^2*(masterWidth c₁ r₀ d y)⁻¹^5)*
      (∑ c : Fin N → Fin 2, ∑ spin : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) spin Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c spin) u) := by
  have hpos := masterWidth_pos hc hr hd y
  have hh := radial_lipschitz_test_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs
    (masterCenteredKernel_lipschitz hg hgs hc hcL hr hd hd1 y)
    (by positivity : 0 < 2*masterWidth c₁ r₀ d y)
    (by linarith : 2*(2*masterWidth c₁ r₀ d y) < t-4*b)
    (masterCenteredKernel_support hg hgs hc hcL hr hd hd1 y)
  change _ ≤ (16*(2*masterWidth c₁ r₀ d y)^3*
    ((masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ d y)⁻¹^4)^2)*_ at hh
  rw [masterRecovery_coefficient hpos] at hh
  exact hh

end CoulombAtom

end

end OAI
