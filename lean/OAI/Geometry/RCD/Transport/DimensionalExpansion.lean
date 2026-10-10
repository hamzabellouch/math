import OAI.Geometry.RCD.Heat.HeatReferenceEVI
import OAI.Geometry.RCD.Metric.DimensionalEvolution

namespace OAI

/-! # Two-speed transport expansion for the actual RCD heat semigroup -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.heat_dimensional_expansion_positive
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {α β a b : ℝ} (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) (hab : a ≤ b) :
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (α*b) f)
      (heatMeasure (hausdorff n X) hX.quadratic (β*b) g)).toReal ≤
    gronwallBound
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (α*a) f)
        (heatMeasure (hausdorff n X) hX.quadratic (β*a) g)).toReal
      (-K*(α+β)) (2*N*(Real.sqrt α-Real.sqrt β)^2) (b-a) := by
  let μ := hausdorff n X
  let D := fun u v => (wassersteinSq (heatMeasure μ hX.quadratic u f)
    (heatMeasure μ hX.quadratic v g)).toReal
  let P := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
  let Q := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t g)
  have hNp : 0 < N := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)) hN
  apply dimensional_evi_expansion (D := D) (P := P) (Q := Q) hK hNp hα hβ ha hab
  · intro u v _ _
    exact ENNReal.toReal_nonneg
  · intro u v hu hv
    exact hX.heat_two_cost_continuousAt K n hn p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs hu hv
  · intro t ht
    exact hX.heat_entropy_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ ht
  · intro t ht
    exact hX.heat_entropy_continuousAt K n hn p g hg0 ⟨rg,hgs⟩ ht
  · intro u v s hu huv hs
    simpa only [D,P,Q,dimensionalEntropyRate,max_eq_left ENNReal.toReal_nonneg] using
      hX.heat_reference_dimensional_EVI K n hn hK hN p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs hs hu huv
  · intro u v s hu huv hs
    have hh := hX.heat_reference_dimensional_EVI K n hn hK hN p g f C
      hg0 hgC hgm hgs hf0 hfC hfm hfs hs hu huv
    simpa only [D,P,Q,dimensionalEntropyRate,max_eq_left ENNReal.toReal_nonneg,
      wassersteinSq_symm (heatMeasure μ hX.quadratic s f)] using hh

end RegularPointCoordinates

end

end OAI
