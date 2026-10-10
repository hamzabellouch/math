import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Sampling.BlockPhaseConstruction
import OAI.Analysis.IrrationalRotation.Product.ProductSourceTagAttenuation

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.ProductScaleLaws

theorem ae_all_source_tagged_ratios {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (j : ℕ) (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Set.Icc (1 / p.N j) (2 / p.N j))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ProductCocycle.Space ℕ)
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ ProductCocycle.haar ℕ)
    (hacy : μ.map y ≪ ProductCocycle.haar ℕ)
    (horder : ∀ᵐ ω ∂μ, ∀ i,
      ProductCocycle.representative (x ω i) ≤ ProductCocycle.representative (y ω i))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E →
      ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
        ProductCocycle.representative (x ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ ProductCocycle.representative (y ω i)) :
    ∀ᵐ ω ∂μ, ω ∈ E → ∀ k : ℤ,
      (p.K j : ℝ) < |(k : ℝ)| → |(k : ℝ)| ≤ p.N j / 4 →
      ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
        ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) ≤
          Real.exp (-p.L j) := by
  have hC (s : ℕ) : p.L s ≤ p.C s := by
    rw [hp.C_eq s]
    exact le_max_left _ _
  have hcost (i : ℕ) (hi : i ∈ ProductPhases.consecutiveBlock p.m j) :
      p.L j ≤ p.C (e i).1 := by
    rw [ProductPhases.enumeration_block_of_mem p.m e he hi]
    exact hC j
  exact ProductCocycle.ae_all_source_tagged_ratios_of_map_ac μ θ
    (fun i => p.C (e i).1) hθ0 hθ
    (fun i => (by norm_num : (0 : ℝ) ≤ 1).trans
      ((hp.L_ge_one (e i).1).trans (hC (e i).1)))
    x y hx hy hacx hacy horder (p.m j) (p.K j) (p.L j)
    (by exact_mod_cast (show 4 ≤ p.m j by have := hp.m_ge_100 j; omega))
    (by exact_mod_cast hp.K_pos j)
    (ProductPhases.consecutiveBlock p.m j)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2) hcost E htag

end Invariant233.ProductScaleLaws

end

end OAI
