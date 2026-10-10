import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeGaugeExtension

namespace OAI

/-! Local equality of scalar representatives transfers their physical gauge derivative. -/

open Set Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalGaugePair_hasDerivAt_of_eqOn (Q f g F G : ℝ → ℂ)
    (s : Set ℝ) (hs : IsOpen s) (hf : EqOn f F s) (hg : EqOn g G s)
    (r : ℝ) (hr : r ∈ s) (A : E₄ → E₄)
    (hD : HasDerivAt (spectralPhysicalGaugePair Q F G)
      (A (spectralPhysicalGaugePair Q F G r)) r) :
    HasDerivAt (spectralPhysicalGaugePair Q f g)
      (A (spectralPhysicalGaugePair Q f g r)) r := by
  have heq : spectralPhysicalGaugePair Q f g =ᶠ[nhds r] spectralPhysicalGaugePair Q F G := by
    filter_upwards [hs.mem_nhds hr] with t ht
    apply spectralPhysicalGaugePair_congr
    · filter_upwards [hs.mem_nhds ht] with x hx
      exact hf hx
    · filter_upwards [hs.mem_nhds ht] with x hx
      exact hg hx
  exact (hD.congr_of_eventuallyEq heq).congr_deriv (congrArg A heq.eq_of_nhds).symm

end DefocusingNLS

end OAI
