import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalAttenuation
import OAI.Analysis.IrrationalRotation.Sampling.ProductStrictPhaseBounds

namespace OAI

noncomputable section
open MeasureTheory Function Set

namespace Invariant233.ProductCocycle

theorem ae_source_tagged_ratio_le_exp_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : Summable θ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → Space ι) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i))
    (m K L : ℝ) (hm : 4 ≤ m) (hK : 0 < K) (k : ℤ)
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (I : Finset ι) (hlo : ∀ i ∈ I, 1 / (m * K) ≤ θ i)
    (hhi : ∀ i ∈ I, θ i ≤ 2 / (m * K)) (hcost : ∀ i ∈ I, L ≤ c i)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ I,
      representative (x ω i) < 1 / m ∧ 1 - 1 / m ≤ representative (y ω i)) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ Real.exp (-L) := by
  filter_upwards [ae_all_int_ratio_bounds_of_map_ac μ θ c hθ0 hθ hc x y
    hx hy hacx hacy horder, htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  have hcross := FloorCocycle.tagged_crossing_of_source_window k hm hK
    (hlo i hi) (hhi i hi) hklo hkhi hxi hyi
  exact ((hr k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

theorem ae_all_source_tagged_ratios_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : Summable θ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → Space ι) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i))
    (m K L : ℝ) (hm : 4 ≤ m) (hK : 0 < K)
    (I : Finset ι) (hlo : ∀ i ∈ I, 1 / (m * K) ≤ θ i)
    (hhi : ∀ i ∈ I, θ i ≤ 2 / (m * K)) (hcost : ∀ i ∈ I, L ≤ c i)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ I,
      representative (x ω i) < 1 / m ∧ 1 - 1 / m ≤ representative (y ω i)) :
    ∀ᵐ ω ∂μ, ω ∈ E → ∀ k : ℤ,
      K < |(k : ℝ)| → |(k : ℝ)| ≤ m * K / 4 →
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ Real.exp (-L) := by
  filter_upwards [ae_all_int_ratio_bounds_of_map_ac μ θ c hθ0 hθ hc x y
    hx hy hacx hacy horder, htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  intro k hklo hkhi
  have hcross := FloorCocycle.tagged_crossing_of_source_window k hm hK
    (hlo i hi) (hhi i hi) hklo hkhi hxi hyi
  exact ((hr k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

end Invariant233.ProductCocycle

end

end OAI
