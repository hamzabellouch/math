import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModeNoExtraLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCompactExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSpectralClassification

namespace OAI

/-! Exact classification on each fixed compact spectral set for all large matched powers. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_compact_classification (hRou : RectangleRouche)
    (ell N : ℕ) (hN : 7 ≤ N) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ lam ∈ K, -(1/32 : ℝ) ≤ lam.re →
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) →
      (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2) := by
  classical
  by_contra h
  have hbad : ∃ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧ ∃ lam ∈ K, -(1/32 : ℝ) ≤ lam.re ∧
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) ∧
      ¬ ((ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2)) := by
    apply (not_eventually.mp h).mono
    intro n hn
    simpa only [not_forall,not_imp,not_not,exists_prop] using hn
  obtain ⟨φ,hφ,hbadφ⟩ := exists_seq_forall_of_frequently hbad
  choose z hX hm lam hmem hhalf hu hnot using hbadφ
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
  have hhalf₀ : -(1/32 : ℝ) ≤ (x₀.2 : ℂ).re :=
    isClosed_Ici.mem_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlam)
      (Eventually.of_forall fun i => hhalf (σ (τ i)))
  have hsym := (radialFree_spectral_zero_iff hRou (profileMatchingParameter x₀.1)
    hp.2 ell x₀.2 hhalf₀).mp hzero
  apply radialMatchedMode_no_extra_limit hRou ell N hN (φ ∘ σ ∘ τ) (hs.comp hτ)
    (fun i => z (σ (τ i))) x₀.1 hz (fun i => hX (σ (τ i))) (fun i => hm (σ (τ i)))
    (fun i => lam (σ (τ i))) x₀.2 hlam hsym
  · exact Eventually.of_forall (fun i he => hnot (σ (τ i)) (by simpa only [he] using hsym))
  · exact fun i => hhalf (σ (τ i))
  · exact fun i => Classical.choice (hu (σ (τ i)))

end DefocusingNLS

end OAI
