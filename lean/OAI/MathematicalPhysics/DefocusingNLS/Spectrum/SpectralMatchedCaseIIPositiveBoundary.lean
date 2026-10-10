import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIOscillatoryBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIRobinData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellInwardLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleValueDerivative

namespace OAI

/-! The positive channel of an actual normalized Case II eigenpair
vanishes at the far boundary of the fixed shell. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_positive_boundary
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
    (hnorm : ∀ i, (∫ r in R..B, spectralPhysicalShellDensity (f i) (g i) r) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (Real.sqrt (lam (φ n)).im : ℂ)*
        (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).1.1) atTop (𝓝 0) ∧
      Tendsto (fun n => (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).1.2) atTop (𝓝 0) := by
  obtain ⟨φ,M,hφ,hM,henergy⟩ := spectralMatched_caseII_oscillatory_bound s hs z z0 hz hX hmatch
    N hN lam ell hhalf hupper hw C R B hC hR hRB hCR hangular f g hf hg he hbounded hL2f hL2g hnorm
  obtain ⟨ψ,A,hψ,hA,hrobin⟩ := spectralMatched_caseII_robin_data (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i)) N hN
    (lam ∘ φ) (ell ∘ φ) (fun i => hhalf (φ i)) (fun i => hupper (φ i))
    (hw.comp hφ.tendsto_atTop) C R B hC hR hRB.le hCR
    (hφ.tendsto_atTop.eventually hangular) (f ∘ φ) (g ∘ φ)
    (fun i => hf (φ i)) (fun i => hg (φ i)) (fun i => he (φ i))
    (fun i => hbounded (φ i)) (fun i => hL2f (φ i)) (fun i => hL2g (φ i))
  let p := fun n r => spectralPhysicalLiouvillePair (f (φ (ψ n))) (g (φ (ψ n))) r
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hpc n : ContinuousOn (p n) (Icc R B) :=
    spectralPhysicalLiouvillePair_continuous_shell R B hR0 _ _ (hf _) (hg _)
  have hgood : ∀ᶠ n in atTop, ∃ a ∈ Icc R ((R+B)/2),
      (lam (φ (ψ n))).im*‖(p n a).1.1‖^2 ≤ M ∧
      ∀ r ∈ Icc a B, (lam (φ (ψ n))).im*‖(p n r).2.1‖^2 ≤ M := by
    filter_upwards [hψ.tendsto_atTop.eventually henergy] with n hn
    obtain ⟨a,ha,hqa,hwa⟩ := hn
    refine ⟨a,ha,hqa,?_⟩
    intro r hr
    have hi := hwa r hr
    dsimp only at hi
    nlinarith only [hi,sq_nonneg ‖(p n r).2.2‖]
  obtain ⟨χ,hχ,hvalue,hderiv⟩ := spectralShell_inward_limit
    (fun n => (lam (φ (ψ n))).im) R B (C/R^2+11) A M hRB (by positivity) hA hM
    (hw.comp (hφ.comp hψ).tendsto_atTop) (fun n r => (p n r).1.1)
    (fun n r => (p n r).1.2) (fun n r => (p n r).2.1) (fun n => (hpc n).fst.fst)
    (fun n r hr => (spectralPhysicalLiouvillePair_value_hasDerivAt r
      (hR0.trans hr.1) _ _ (hf _) (hg _)).1) hgood hrobin
  exact ⟨φ ∘ ψ ∘ χ,hφ.comp (hψ.comp hχ),hvalue,hderiv⟩

end DefocusingNLS

end OAI
