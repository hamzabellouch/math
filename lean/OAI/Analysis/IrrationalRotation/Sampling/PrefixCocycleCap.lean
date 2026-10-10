import OAI.Analysis.IrrationalRotation.Couplings.PrefixHybrid
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle

namespace OAI

noncomputable section
open MeasureTheory Function Set

namespace Invariant233.ProductModel

theorem finite_floor_support_selectedEndpoint
    (θ : ℕ → ℝ) (k : ℤ) (x y : Base) (I : Finset ℕ)
    (hx : HasFiniteSupport (fun i =>
      ⌊circleRepresentative (x i) + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport (fun i =>
      ⌊circleRepresentative (y i) + (k : ℝ) * θ i⌋)) :
    HasFiniteSupport (fun i =>
      ⌊circleRepresentative (selectedEndpoint I x y i) + (k : ℝ) * θ i⌋) := by
  apply (hx.union hy).subset
  intro i hi
  by_cases hI : i ∈ I
  · right
    simpa only [Function.mem_support, selectedEndpoint, ite_eq_left hI] using hi
  · left
    simpa only [Function.mem_support, selectedEndpoint, ite_eq_right hI] using hi

theorem ae_pair_all_int_finite_floor_support
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure) :
    ∀ᵐ xy ∂ν, ∀ k : ℤ,
      HasFiniteSupport (fun i =>
        ⌊circleRepresentative (xy.1 i) + (k : ℝ) * θ i⌋) ∧
      HasFiniteSupport (fun i =>
        ⌊circleRepresentative (xy.2 i) + (k : ℝ) * θ i⌋) := by
  have hbase : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      HasFiniteSupport (fun i =>
        ⌊circleRepresentative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  have hx := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hbase)
  have hy := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hbase)
  filter_upwards [hx, hy] with xy hx hy
  exact fun k => ⟨hx k, hy k⟩

theorem ae_ordered_cocycle_ratio_cap
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂ν, ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
  filter_upwards [ae_pair_all_int_finite_floor_support θ hθ0 hθ ν hfst hsnd,
    horder] with xy hs ho
  intro k
  exact ⟨div_pos (ProductCocycle.cocycleVersion_pos θ c k xy.2)
      (ProductCocycle.cocycleVersion_pos θ c k xy.1),
    ProductCocycle.cocycleVersion_ratio_le_one θ c k xy.1 xy.2 hc ho
      (hs k).1 (hs k).2⟩

theorem ae_all_selected_cocycle_ratio_cap
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂ν, ∀ (I : Finset ℕ) (k : ℤ),
      0 < ProductCocycle.cocycleVersion θ c k (selectedEndpoint I xy.1 xy.2) /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k (selectedEndpoint I xy.1 xy.2) /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
  filter_upwards [ae_pair_all_int_finite_floor_support θ hθ0 hθ ν hfst hsnd,
    horder] with xy hs ho
  intro I k
  exact ⟨div_pos (ProductCocycle.cocycleVersion_pos θ c k _)
      (ProductCocycle.cocycleVersion_pos θ c k _),
    ProductCocycle.cocycleVersion_ratio_le_one θ c k xy.1
      (selectedEndpoint I xy.1 xy.2) hc (ordered_selectedEndpoint ho I).1
      (hs k).1 (finite_floor_support_selectedEndpoint θ k xy.1 xy.2 I
        (hs k).1 (hs k).2)⟩

theorem measurableSet_all_cocycle_ratio_cap (θ c : ℕ → ℝ) :
    MeasurableSet {xy : EndpointPair | ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1} := by
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hm := ((ProductCocycle.measurable_cocycleVersion θ c k).comp measurable_snd).div
    ((ProductCocycle.measurable_cocycleVersion θ c k).comp measurable_fst)
  exact (measurableSet_lt measurable_const hm).inter
    (measurableSet_le hm measurable_const)

theorem prefixPairLaw_cocycle_ratio_cap
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) (D : ℕ) :
    ∀ᵐ xy ∂prefixPairLaw ν D, ∀ k : ℤ,
      0 < ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ∧
      ProductCocycle.cocycleVersion θ c k xy.2 /
        ProductCocycle.cocycleVersion θ c k xy.1 ≤ 1 := by
  rw [prefixPairLaw, ae_map_iff (measurable_prefixPair D).aemeasurable
    (measurableSet_all_cocycle_ratio_cap θ c)]
  filter_upwards [ae_all_selected_cocycle_ratio_cap θ c hθ0 hθ hc ν hfst hsnd horder]
    with xy hxy
  exact hxy (Finset.range D)

end Invariant233.ProductModel

end

end OAI
