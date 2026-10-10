import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSpectralLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingParameterLimit
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! Compact subsets disjoint from the free outgoing zeros eventually contain
no actual radial eigenvalues. The matching equations determine the limiting
profile internally. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_limit_zero_of_matching
    (ell N : ℕ) (hN : 7 ≤ N) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (lam : ℕ → ℂ) (lam₀ : ℂ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hhalf : ∀ i, -(1/32 : ℝ)≤(lam i).re)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (lam i)) :
    spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) lam₀=0 := by
  obtain ⟨hz₁,hz₀⟩ := radialMatchingMap_zero_limit s hs.tendsto_atTop z z₀ hz hm
  have hhalf₀ : -(1/32 : ℝ)≤lam₀.re :=
    isClosed_Ici.mem_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlam)
      (Eventually.of_forall hhalf)
  exact radialMatchedSpectralMode_limit_zero ell N hN s hs z z₀ hz hX hm hz₁ hz₀
    lam lam₀ hlam hhalf₀ hhalf mode

theorem radialMatchedSpectralMode_compact_exclusion
    (ell N : ℕ) (hN : 7 ≤ N) (K : Set ℂ) (hK : IsCompact K)
    (hfree : ∀ z₀ : ProfileMatchingBall, z₀.val.1=0 →
      diskProfile (profileMatchingParameter z₀)=0 → ∀ lam ∈ K,
      -(1/32 : ℝ)≤lam.re →
      spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
        ((radialShootingR (profileMatchingParameter z₀))^2/4) lam≠0) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ lam ∈ K, -(1/32 : ℝ)≤lam.re →
      ¬ Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) := by
  classical
  by_contra h
  have hbad : ∃ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧ ∃ lam ∈ K, -(1/32 : ℝ)≤lam.re ∧
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) := by
    apply (not_eventually.mp h).mono
    intro n hn
    simpa only [not_forall,not_imp,not_not,exists_prop] using hn
  obtain ⟨φ,hφ,hbadφ⟩ := exists_seq_forall_of_frequently hbad
  choose z hX hm lam hmem hhalf hu using hbadφ
  obtain ⟨σ,_hσ,hs⟩ := strictMono_subseq_of_tendsto_atTop hφ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let x : ℕ → ProfileMatchingBall × K := fun i => (z (σ i),⟨lam (σ i),hmem (σ i)⟩)
  obtain ⟨x₀,τ,hτ,hx⟩ := CompactSpace.tendsto_subseq x
  have hz : Tendsto (fun i => z (σ (τ i))) atTop (𝓝 x₀.1) := hx.fst_nhds
  have hlam : Tendsto (fun i => lam (σ (τ i))) atTop (𝓝 (x₀.2 : ℂ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hx.snd_nhds
  have hp := radialMatchingMap_zero_limit (φ ∘ σ ∘ τ) (hs.comp hτ).tendsto_atTop
    (fun i => z (σ (τ i))) x₀.1 hz (fun i => hm (σ (τ i)))
  have hzero := radialMatchedSpectralMode_limit_zero_of_matching ell N hN
    (φ ∘ σ ∘ τ) (hs.comp hτ) (fun i => z (σ (τ i))) x₀.1 hz
    (fun i => hX (σ (τ i))) (fun i => hm (σ (τ i)))
    (fun i => lam (σ (τ i))) x₀.2 hlam (fun i => hhalf (σ (τ i)))
    (fun i => Classical.choice (hu (σ (τ i))))
  exact hfree x₀.1 hp.1 hp.2 x₀.2 x₀.2.property
    (isClosed_Ici.mem_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlam)
      (Eventually.of_forall fun i => hhalf (σ (τ i)))) hzero

end DefocusingNLS

end OAI
