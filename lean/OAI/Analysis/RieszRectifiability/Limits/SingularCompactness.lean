import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.LimitEnergy
import OAI.Analysis.RieszRectifiability.Limits.LocalSingularLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem singular_compactness_of_weak_moments {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (hgν : GlobalUpperGrowth (p + 1) C (ν : Measure (Ambient d)))
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (hwm : ∀ j, Measurable (w j)) (hv : MemLp v 2 (ν : Measure (Ambient d))) (hvm : Measurable v)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (htotal : ∀ j, (μ j : Measure (Ambient d)).real univ ≤ M)
    (hsecond : ∀ j, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ M)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 (ν : Measure (Ambient d)) → (∀ j, MemLp ψ 2 (μ j : Measure (Ambient d))) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, v x * ψ x ∂(ν : Measure (Ambient d)))))
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (E : ℝ) (hE : ∀ j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) v q.1 q.2)
      ((ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) v q.1 q.2
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ≤ E ∧
      ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ → (∀ x, |φ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
          (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2
            ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  have hM : 0 ≤ M := measureReal_nonneg.trans (htotal 0)
  have ht : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M :=
    Filter.Eventually.of_forall htotal
  have hsec : ∀ᶠ j in atTop, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ M :=
    Filter.Eventually.of_forall hsecond
  obtain ⟨hvE, hvEbound⟩ := limiting_fractional_energy_bound (p + 1) μ ν hweak w v hw hv hvm
    ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M hM ht hsec hmoment henergy E hE
  refine ⟨hvE, hvEbound, ?_⟩
  intro φ L B hφ hB
  apply fractional_bilinear_tendsto_of_capped p C (fun j => (μ j : Measure (Ambient d)))
    (ν : Measure (Ambient d)) hg hgν w v hwm hvm (fun j => (hw j).integrable (by norm_num))
    (hv.integrable (by norm_num)) henergy hvE E M hE htotal φ L B hφ hB
  intro ε hε
  exact capped_bilinear_tendsto (fun j => (μ j : Measure (Ambient d))) (ν : Measure (Ambient d))
    w v hw hv ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M hM ht hsec hmoment
    (p + 1) ε hε φ L B hφ hB

end

end RieszRectifiability

end OAI
