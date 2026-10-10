import OAI.Geometry.RCD.Transport.WeightedMatchedOptimality

namespace OAI

/-! # A bounded geodesic triplet law extends to a compressed optimal plan

The two half plans are constructed from curvature-dimension transport.
Sharp quadratic saturation proves their concatenation is geodesic.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {A X : Type*} [MeasurableSpace A] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)]
attribute [local instance] pathBorel pathBorelSpace

omit [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem complete_optimal_triplets (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (P : Measure A) [IsProbabilityMeasure P]
    (x a b : A → X) (hx : Measurable x) (ha : Measurable a) (hb : Measurable b)
    (t : Ioo (0:ℝ) 1)
    (hp : IsOptimalCoupling (P.map a) (P.map b) (P.map (fun z => (a z,b z))))
    (hgeo : ∀ᵐ z ∂P, dist (x z) (a z)=(t:ℝ)*dist (a z) (b z) ∧
      dist (x z) (b z)=(1-(t:ℝ))*dist (a z) (b z))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcx : P.map x ≤ C • hausdorff n X)
    (hca : P.map a ≤ C • hausdorff n X)
    (hcb : P.map b ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hsx : ∀ᵐ y ∂P.map x, dist y p ≤ R)
    (hsa : ∀ᵐ y ∂P.map a, dist y p ≤ R)
    (hsb : ∀ᵐ y ∂P.map b, dist y p ≤ R) :
    ∃ τ : Measure C(Time,X), IsProbabilityMeasure τ ∧
      (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling (P.map a) (P.map b) (τ.map (fun γ => (γ 0,γ 1))) ∧
      τ.map (fun γ => γ ⟨t,t.property.1.le,t.property.2.le⟩)=P.map x ∧
      ∀ s : Time, τ.map (fun γ => γ s) ≤ compressionBudget K n (2*R) C • hausdorff n X := by
  let : Nonempty X := ⟨p⟩
  let : IsProbabilityMeasure (P.map x) := inferInstance
  let : IsProbabilityMeasure (P.map a) := inferInstance
  let : IsProbabilityMeasure (P.map b) := inferInstance
  obtain ⟨q₀,hq₀,hg₀,hp₀,_,hc₀⟩ := hX.exists_bounded_entropy_plan K n hn
    (P.map a) (P.map x) hC hca hcx p hR hsa hsx
  obtain ⟨q₁,hq₁,hg₁,hp₁,_,hc₁⟩ := hX.exists_bounded_entropy_plan K n hn
    (P.map x) (P.map b) hC hcx hcb p hR hsx hsb
  let := hq₀
  let := hq₁
  have he₀ := optimalPlan_endpoints _ _ q₀ hp₀
  have he₁ := optimalPlan_endpoints _ _ q₁ hp₁
  obtain ⟨ρ,hρ,hρ₀,hρ₁⟩ := exists_matched_path_law q₀ q₁ (he₀.2.trans he₁.1.symm)
  let := hρ
  have hfin := finite_second_moment_cost (finiteSecondMoment_of_bounded (P.map a) p hsa)
    (finiteSecondMoment_of_bounded (P.map b) p hsb) hp.1 hp.2.1
  obtain ⟨hopt,hg⟩ := weighted_matched_law_optimal P x a b hx ha hb t hp hfin hgeo
    q₀ q₁ hg₀ hg₁ hp₀ hp₁ ρ hρ₀ hρ₁
  refine ⟨ρ.map (weightedJoin t),inferInstance,
    hg,hopt,(weightedJoin_law_split t ρ q₀ hρ₀).trans he₀.2,?_⟩
  intro s
  by_cases hs : (s:ℝ) ≤ t
  · rw [weightedJoin_law_left t ρ q₀ hρ₀ s hs]
    exact (hc₀ _).1
  · rw [weightedJoin_law_right t ρ q₁ hρ₁ s (le_of_not_ge hs)]
    exact (hc₁ _).1

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
