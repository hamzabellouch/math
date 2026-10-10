import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralExpansionUniqueness

namespace OAI

/-! A column constructed at one fixed sufficient order is the canonical
all-orders column on their common exterior ray. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circular_expansion_matches_allOrders
    (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n) (c : ℂ × ℂ)
    (j : ℕ) (v : CircularTailSpace) (M T : ℝ) (hT : 0 ≤ T)
    (q : ℝ → ℂ) (Z W : ℝ → E₄)
    (hq : ∀ t, T ≤ t → ‖q t‖ ≤ M)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η n (q t) (Z t)) t)
    (hW : ∀ t, T ≤ t → HasDerivAt W
      (circularLeadingField t (W t)+circularBoundedField νp νm η n (q t) (W t)) t)
    (heZ : ∀ t, T ≤ t → Z t=circularPolynomialJet
      (spectralOutgoingPolynomial νp νm η n (radialExteriorExpansion ν n b j) c j) t+
        circularUnweight (2*(j : ℝ)) v t)
    (heW : ∀ J : ℕ, ∃ k : ℕ, J ≤ k ∧ ∃ w : CircularTailSpace, ∀ t, 0 ≤ t →
      W t=circularPolynomialJet
        (spectralOutgoingPolynomial νp νm η n (radialExteriorExpansion ν n b k) c k) t+
          circularUnweight (2*(k : ℝ)) w t)
    (hgap : circularFieldBound νp νm η n M < 2*(j : ℝ)) :
    ∀ t, T ≤ t → Z t=W t := by
  obtain ⟨k,hjk,w,hw⟩ := heW j
  have heq := circular_outgoing_orders_unique ν νp νm η b n hn c j k hjk v w M T q Z W
    hq hZ hW heZ (fun t ht => hw t (hT.trans ht)) hgap
  simpa only [max_eq_left hT] using heq

end DefocusingNLS

end OAI
