import OAI.Analysis.IrrationalRotation.Model.ProductPairIdentity
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawProperties
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingAbsoluteContinuity
import OAI.Analysis.IrrationalRotation.Rotation.UnrestrictedDiagonal

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cocycleRatio_pos (θ c : ℕ → ℝ) (x y : Base) (k : ℤ) :
    0 < cocycleRatio θ c x y k :=
  div_pos (ProductCocycle.cocycleVersion_pos θ c k y)
    (ProductCocycle.cocycleVersion_pos θ c k x)

theorem ae_all_cocycleRatio_bounds_of_ordered
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂ν, ∀ k : ℤ,
      0 < cocycleRatio θ c xy.1 xy.2 k ∧
        cocycleRatio θ c xy.1 xy.2 k ≤ 1 := by
  have hcore := CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  have hfirst := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hcore)
  have hsecond := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hcore)
  filter_upwards [hfirst, hsecond, horder] with xy hx hy hxy
  intro k
  refine ⟨cocycleRatio_pos θ c xy.1 xy.2 k, ?_⟩
  exact ProductCocycle.cocycleVersion_ratio_le_one θ c k xy.1 xy.2
    hc hxy (hx k) (hy k)

theorem triangularLaw_ae_all_cocycleRatio_bounds
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (I : Finset ℕ) :
    ∀ᵐ xy ∂triangularLaw I, ∀ k : ℤ,
      0 < cocycleRatio θ c xy.1 xy.2 k ∧
        cocycleRatio θ c xy.1 xy.2 k ≤ 1 := by
  apply ae_all_cocycleRatio_bounds_of_ordered θ c hθ0 hθ hc (triangularLaw I)
  · rw [Sampling.triangularLaw_first_marginal]
    exact withDensity_absolutelyContinuous _ _
  · rw [Sampling.triangularLaw_second_marginal]
    exact withDensity_absolutelyContinuous _ _
  · exact Sampling.triangularLaw_ordered I

theorem HasUniformL2Marginals.ae_all_cocycleRatio_bounds
    {η : ℕ → Measure EndpointPair} (hη : HasUniformL2Marginals η)
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (horder : ∀ l, ∀ᵐ xy ∂η l, Ordered xy.1 xy.2) :
    ∀ l, ∀ᵐ xy ∂η l, ∀ k : ℤ,
      0 < cocycleRatio θ c xy.1 xy.2 k ∧
        cocycleRatio θ c xy.1 xy.2 k ≤ 1 := by
  intro l
  obtain ⟨H, hH, hdens⟩ := hη
  obtain ⟨f, g, hf, hg, hmf, hmg, hbf, hbg⟩ := hdens l
  apply ae_all_cocycleRatio_bounds_of_ordered θ c hθ0 hθ hc (η l)
  · rw [hmf]
    exact withDensity_absolutelyContinuous _ _
  · rw [hmg]
    exact withDensity_absolutelyContinuous _ _
  · exact horder l

end Invariant233.ProductModel

end

end OAI
