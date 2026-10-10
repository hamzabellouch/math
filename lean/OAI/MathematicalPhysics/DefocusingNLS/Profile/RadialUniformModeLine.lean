import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModeLine
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralClassification

namespace OAI

/-! # Uniform one-dimensionality of the actual symmetry radial modes -/

open Filter Topology Set

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_eventually_mode_line (hRou : RectangleRouche)
    (ell N : ℕ) (hN : 7 ≤ N) (lam : ℂ)
    (hsym : (ell = 0 ∧ (lam = 0 ∨ lam = 1)) ∨ (ell = 1 ∧ lam = 1 / 2)) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z = 0 → RadialModeLine n z ell N lam := by
  classical
  by_contra h
  have hbad : ∃ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z = 0 ∧ ¬ RadialModeLine n z ell N lam := by
    apply (not_eventually.mp h).mono
    intro n hn
    simpa only [not_forall, not_imp, exists_prop] using hn
  obtain ⟨φ, hφ, hbadφ⟩ := exists_seq_forall_of_frequently hbad
  choose z hX hm hn using hbadφ
  obtain ⟨σ, _, hσ⟩ := strictMono_subseq_of_tendsto_atTop hφ
  obtain ⟨z₀, τ, hτ, hz⟩ := CompactSpace.tendsto_subseq (fun i => z (σ i))
  obtain ⟨i, hi⟩ := radialMatched_mode_line_along hRou ell N hN lam hsym
    (φ ∘ σ ∘ τ) (hσ.comp hτ) (fun i => z (σ (τ i))) z₀ hz
    (fun i => hX (σ (τ i))) (fun i => hm (σ (τ i)))
  exact hn (σ (τ i)) hi

theorem radialMatched_eventually_all_mode_lines (hRou : RectangleRouche) (N : ℕ) (hN : 7 ≤ N) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z = 0 → ∀ ell : ℕ, ∀ lam : ℂ, -(1 / 32 : ℝ) ≤ lam.re →
        RadialModeLine n z ell N lam := by
  filter_upwards [radialMatched_eventually_mode_line hRou 0 N hN 0 (by simp),
    radialMatched_eventually_mode_line hRou 0 N hN 1 (by simp),
    radialMatched_eventually_mode_line hRou 1 N hN (1 / 2) (by simp),
    radialMatchedSpectralMode_classification hRou N hN] with n h0 h1 hh hc
  intro z hX hz ell lam hl u v
  have hη : (((ell : ℝ) * (ell + 10) : ℝ) : ℂ) = (ell : ℂ) * (ell + 10) := by
    push_cast
    rfl
  have hs := hc z hX hz ell lam hl (by simpa only [hη] using Nonempty.intro u)
  rcases hs with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact h0 z hX hz u v
  · exact h1 z hX hz u v
  · exact hh z hX hz u v

end DefocusingNLS

end OAI
