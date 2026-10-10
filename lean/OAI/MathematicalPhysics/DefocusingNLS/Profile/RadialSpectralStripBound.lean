import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedEscapeExclusion

namespace OAI

/-! Exclusion of escaping mode sequences gives a uniform angular/frequency
bound for all sufficiently large matched powers in the counting strip. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_strip_bound (N : ℕ) (hN : 7 ≤ N) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ ell : ℕ, ∀ lam : ℂ,
      -(1/32 : ℝ) ≤ lam.re → lam.re ≤ 4 → 0 ≤ lam.im →
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam) →
      (ell : ℝ)+lam.im ≤ M := by
  classical
  by_contra hn
  have hbad : ∀ M : ℝ, ∃ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧ ∃ ell : ℕ, ∃ lam : ℂ,
      -(1/32 : ℝ) ≤ lam.re ∧ lam.re ≤ 4 ∧ 0 ≤ lam.im ∧
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam) ∧
      M < (ell : ℝ)+lam.im := by
    simpa only [not_exists,not_eventually,not_forall,not_imp,not_le,not_not,exists_prop] using hn
  have hchoose (j : ℕ) : ∃ n : ℕ, j ≤ n ∧ ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧ ∃ ell : ℕ, ∃ lam : ℂ,
      -(1/32 : ℝ) ≤ lam.re ∧ lam.re ≤ 4 ∧ 0 ≤ lam.im ∧
      Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam) ∧
      (j : ℝ) < (ell : ℝ)+lam.im := by
    obtain ⟨n,hdata,hjn⟩ := ((hbad (j : ℝ)).and_eventually (eventually_ge_atTop j)).exists
    exact ⟨n,hjn,hdata⟩
  choose s hs z hX hm ell lam hl hu hi mode hlarge using hchoose
  have hsTop : Tendsto s atTop atTop := tendsto_atTop_mono hs tendsto_id
  obtain ⟨σ,hσ,hsσ⟩ := strictMono_subseq_of_tendsto_atTop hsTop
  obtain ⟨z0,τ,hτ,hz⟩ := CompactSpace.tendsto_subseq (z ∘ σ)
  let ψ := σ ∘ τ
  have hψ : StrictMono ψ := hσ.comp hτ
  have hsz : StrictMono (s ∘ ψ) := hsσ.comp hτ
  have hz' : Tendsto (z ∘ ψ) atTop (𝓝 z0) := hz
  have hescape : Tendsto (fun i => (ell (ψ i) : ℝ)+(lam (ψ i)).im) atTop atTop := by
    apply tendsto_atTop_mono (fun i => (hlarge (ψ i)).le)
    exact tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
  exact spectralMatched_escape_exclusion (s ∘ ψ) hsz (z ∘ ψ) z0 hz'
    (fun i => hX (ψ i)) (fun i => hm (ψ i)) N hN (lam ∘ ψ) (ell ∘ ψ)
    (fun i => hl (ψ i)) (fun i => hu (ψ i)) (fun i => hi (ψ i)) hescape
    (fun i => Classical.choice (mode (ψ i)))

end DefocusingNLS

end OAI
