import OAI.Analysis.IrrationalRotation.Model.ProductScaleSampling
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConstruction
import OAI.Analysis.IrrationalRotation.Analysis.SeparatedPowers

namespace OAI

noncomputable section
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem eventually_exists_sampling_powers :
    ∀ᶠ j : ℕ in atTop, ∃ s : Finset ℕ, ProductSamplingPowersAt p j s := by
  have h := hp.m_strictMono.tendsto_atTop.eventually
    SeparatedPowers.eventually_exists_nat_sampling_powers
  filter_upwards [h] with j hj
  have hN : p.m j * p.K j ≤ p.m j ^ 2 := by
    calc
      _ ≤ p.m j * p.m j := Nat.mul_le_mul_left _ (hp.m_ge_K j)
      _ = _ := by ring
  obtain ⟨s, hrange, hcard, hpos, hsep⟩ := hj (p.m j * p.K j) hN
  exact ⟨s, hrange, hcard, hpos, hsep⟩

theorem exists_sampling_sequence :
    ∃ s : ℕ → Finset ℕ, ∀ᶠ j : ℕ in atTop, ProductSamplingPowersAt p j (s j) := by
  classical
  let s (j : ℕ) : Finset ℕ := if h : ∃ t, ProductSamplingPowersAt p j t then
    Classical.choose h else ∅
  refine ⟨s, ?_⟩
  filter_upwards [hp.eventually_exists_sampling_powers] with j hj
  dsimp [s]
  rw [dite_eq_left hj]
  exact Classical.choose_spec hj

end Invariant233.ProductScaleLaws

namespace Invariant233.ProductScaleConstruction

theorem exists_product_scales_and_sampling :
    ∃ p : ProductScaleData, ProductScaleLaws p ∧
      ∃ s : ℕ → Finset ℕ, ∀ᶠ j : ℕ in atTop, ProductSamplingPowersAt p j (s j) := by
  obtain ⟨p, hp⟩ := exists_product_scales
  exact ⟨p, hp, hp.exists_sampling_sequence⟩

end Invariant233.ProductScaleConstruction

end

end OAI
