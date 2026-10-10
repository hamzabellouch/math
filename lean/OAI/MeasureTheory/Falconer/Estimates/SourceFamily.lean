import OAI.MeasureTheory.Falconer.Estimates.SourceRepresentatives
import OAI.MeasureTheory.Falconer.Estimates.RegularizationPairMask

namespace OAI

/-! # Choosing the actual source family at every sufficiently large scale -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem eventual_source_family (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {s C lam : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) (hC : 0 ≤ C) (hlam : 0 < lam)
    (hball : ∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      0 < N ∧ 0 < B ∧ (B:ℝ) ≤ lam*N ∧
      (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam ∧
      μ (retainedRegion Q μ N B t)ᶜ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t ∧
      ∃ p : List ℕ → CellPath d,
        (∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N) ∧
        (∀ T ∈ regularizationIndex Q μ N B t, regularizationLabel Q μ N B (p T) = T) ∧
        (∀ T ∈ regularizationIndex Q μ N B t,
          RegularizedProfileData Q (sourceClass Q μ N B (p T)) N s lam (sourceUnitProfile Q μ N B (p T))) := by
  obtain ⟨H,N₀,hH,_hHb,h₀⟩ := actual_regular_source_classes hd Q hQ μ hcarry hs hsd hC hlam hball
  refine ⟨H,N₀,hH,?_⟩
  intro N hN
  obtain ⟨hNp,hB,hw,hl,_hcount,hdiscard,hclasses⟩ := h₀ N hN
  refine ⟨hNp,hB,hw,hl,hdiscard,?_⟩
  exact source_representatives Q μ N (N/H) _ s lam (fun T hT => (hclasses T hT).2)

end Falconer.Regularization

end OAI
