import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicSingularLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformAnnulus

namespace OAI

/-! Choose canonical holomorphic columns independently of the spectral parameter. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialShooting_exists_canonical_column (z : ℕ → ProfileMatchingBall)
    (ell : ℕ) (c : ℂ × ℂ) :
    ∃ Y : ℕ → ℂ → ℝ → E₄, ∀ᶠ n in atTop,
      IsCanonicalHolomorphicColumn (radialShootingNu n (z n))
        ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z n)) n
        (Real.log innerBoundaryRadius) c (Y n) := by
  classical
  have hex (n : ℕ) : ∃ Y : ℂ → ℝ → E₄,
      (1 ≤ n ∧ HasRadialExterior (radialShootingNu n (z n)) n
        (radialShootingM (z n)) (Real.log innerBoundaryRadius)) →
      IsCanonicalHolomorphicColumn (radialShootingNu n (z n))
        ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z n)) n
        (Real.log innerBoundaryRadius) c Y := by
    by_cases h : 1 ≤ n ∧ HasRadialExterior (radialShootingNu n (z n)) n
        (radialShootingM (z n)) (Real.log innerBoundaryRadius)
    · obtain ⟨Y,hY⟩ := canonical_holomorphic_circular_allOrders
        (radialShootingNu n (z n)) (radialShootingNu n (z n))
        (star (radialShootingNu n (z n))) ((ell*(ell+10) : ℕ) : ℂ)
        (radialShootingM (z n)) n h.1 (Real.log innerBoundaryRadius) h.2
        (radialShootingM_ne_zero (z n)) c
      exact ⟨Y,fun _ => hY⟩
    · exact ⟨fun _ _ => 0,fun hh => (h hh).elim⟩
  choose Y hY using hex
  refine ⟨Y,?_⟩
  filter_upwards [eventually_ge_atTop 1,radialShootingExterior_exists] with n hn hX
  exact hY n ⟨hn,hX (z n)⟩

theorem radialMatched_exists_canonical_column (s : ℕ → ℕ) (z : ℕ → ProfileMatchingBall)
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (ell : ℕ) (c : ℂ × ℂ) :
    ∃ Y : ℕ → ℂ → ℝ → E₄, ∀ i,
      IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
        ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i)) (s i+radialInnerShootingThreshold)
        (Real.log innerBoundaryRadius) c (Y i) := by
  have hex (i : ℕ) : ∃ Y : ℂ → ℝ → E₄,
      IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
        ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i)) (s i+radialInnerShootingThreshold)
        (Real.log innerBoundaryRadius) c Y :=
    canonical_holomorphic_circular_allOrders _ _ _ _ _ _
      (radialShootingInner_power_pos (s i) (profileMatchingParameter (z i)))
      _ (hX i) (radialShootingM_ne_zero (z i)) c
  exact Classical.axiomOfChoice hex

end DefocusingNLS

end OAI
