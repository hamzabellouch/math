import OAI.MeasureTheory.Falconer.Geometry.TroublesomeCovers
import OAI.MeasureTheory.Falconer.Incidence.RadialIncidenceBound

namespace OAI

/-! # Original-law incidence bound for the actual troublesome-pair relation -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem troublesome_pair_incidence_bound (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : Space (n+1)) {r D δ C B F a R H t : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hF : 0 < F) (ha : 0 < a) (ha1 : a ≤ 1)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (hR : ∀ᵐ p ∂ν, ‖c-p‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      ν {p | |inner ℝ u p-inner ℝ u c| ≤ R*a} ≤ K)
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hball : ∀ p : Space (n+1), μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) ≤ ENNReal.ofReal H)
    (hbudget : (((2*L+1)^(n+1):ℕ)/F)^(n+1)*
      (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/a^(n+1))^(n*(n+1))*H^n ≤ t^n) :
    ((μ.prod ν) (troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F)))^(n+1) ≤
      ENNReal.ofReal t+(n+1:ℝ≥0∞)*K := by
  obtain ⟨A,hcover,hcard⟩ := troublesome_pair_covers μ c hr hδ hF hfreeze hsource L hL
  exact radial_tube_incidence_bound hLW hn μ ν c ha ha1 hR K hslab _
    (troublesomePair_measurable μ c r D B (C*δ) (ENNReal.ofReal F)) A B
    (fun z p hz => hz.2.2.2.1) hδ (Nat.cast_nonneg _) hH ht hball hcover hcard hbudget

end Falconer

end OAI
