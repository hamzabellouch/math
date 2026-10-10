import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIPositiveBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIOutgoingRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingRobinLimit

namespace OAI

/-! The actual Case II shell argument removes both boundary channels
once the exact interior flux is small. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_boundary_from_flux
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R B : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hRB : R < B) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0))
    (hnorm : ∀ i, (∫ r in R..B, spectralPhysicalShellDensity (f i) (g i) r) ≤ 1)
    (hflux : Tendsto (fun i => Real.sqrt (lam i).im*
      (spectralScalarFlux (spectralPhysicalLiouvillePair (f i) (g i) B).1+
        spectralScalarFlux (spectralPhysicalLiouvillePair (f i) (g i) B).2)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (Real.sqrt (lam (φ n)).im : ℂ)*
        (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).1.1) atTop (𝓝 0) ∧
      Tendsto (fun n => (Real.sqrt (lam (φ n)).im : ℂ)*
        (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).2.1) atTop (𝓝 0) ∧
      Tendsto (fun n => (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).1.2) atTop (𝓝 0) ∧
      Tendsto (fun n => (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).2.2) atTop (𝓝 0) := by
  obtain ⟨φ,hφ,hpv,hpd⟩ := spectralMatched_caseII_positive_boundary s hs z z0 hz hX hmatch
    N hN lam ell hhalf hupper hw C R B hC hR hRB hCR hangular f g hf hg he hbounded hL2f hL2g hnorm
  obtain ⟨ψ,A,hψ,hA,hrobin⟩ := spectralMatched_caseII_outgoing_robin_data (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i)) N hN
    (lam ∘ φ) (ell ∘ φ) (fun i => hhalf (φ i)) (fun i => hupper (φ i))
    (hw.comp hφ.tendsto_atTop) C R B hC hR hRB.le hCR
    (hφ.tendsto_atTop.eventually hangular) (f ∘ φ) (g ∘ φ)
    (fun i => hf (φ i)) (fun i => hg (φ i)) (fun i => he (φ i))
    (fun i => hbounded (φ i)) (fun i => hL2f (φ i)) (fun i => hL2g (φ i))
  let q := fun n => spectralPhysicalLiouvillePair (f (φ (ψ n))) (g (φ (ψ n))) B
  let nu := fun n => Real.sqrt (lam (φ (ψ n))).im
  have hnu n : 0 ≤ nu n := Real.sqrt_nonneg _
  have hpv' : Tendsto (fun n => nu n*‖(q n).1.1‖) atTop (𝓝 0) := by
    have ht := tendsto_zero_iff_norm_tendsto_zero.mp (hpv.comp hψ.tendsto_atTop)
    simpa only [Function.comp_def,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using ht
  have hlocal : ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, ∃ alpha : ℂ,
      alpha.im ≤ -nu n/4 ∧ ‖alpha‖ ≤ A*nu n ∧
      ‖(q n).2.2-alpha*(q n).2.1‖ ≤ delta*(C/R^2+11)*nu n*(‖(q n).1.1‖+‖(q n).2.1‖) := by
    intro delta hdelta
    filter_upwards [hrobin delta hdelta] with n hn
    exact hn B ⟨hRB.le,le_rfl⟩
  obtain ⟨χ,hχ,hmv,hmd⟩ := spectralOutgoing_robin_limit nu A (C/R^2+11) (by positivity)
    (fun n => (q n).1.1) (fun n => (q n).2.1) (fun n => (q n).1.2) (fun n => (q n).2.2)
    (Eventually.of_forall hnu) hpv' (hpd.comp hψ.tendsto_atTop)
    (hflux.comp (hφ.comp hψ).tendsto_atTop) hlocal
  refine ⟨φ ∘ ψ ∘ χ,hφ.comp (hψ.comp hχ),hpv.comp (hψ.comp hχ).tendsto_atTop,?_,
    hpd.comp (hψ.comp hχ).tendsto_atTop,hmd⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hmv

end DefocusingNLS

end OAI
