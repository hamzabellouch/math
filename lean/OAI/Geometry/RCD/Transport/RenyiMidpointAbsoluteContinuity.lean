import OAI.Geometry.RCD.Transport.RenyiOptimalMidpoint
import OAI.Geometry.RCD.Transport.RenyiSingularReplacement

namespace OAI

/-! # A Rényi-maximizing midpoint has no singular part -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

def RenyiMaximizingPlan (μ ν₀ ν₁ : Measure X) (π : Measure C(Time,X)) (t : Time) (q : ℝ) : Prop :=
  ∀ κ : Measure C(Time,X), IsProbabilityMeasure κ →
    (∀ᵐ γ ∂κ, IsGeodesic γ) → IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))) →
    (∫ x, ((κ.map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ) ≤
      ∫ x, ((π.map (fun γ => γ t)).rnDeriv μ x).toReal^q ∂μ

theorem NoncollapsedRCD.renyi_midpoint_absolutelyContinuous
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmax : RenyiMaximizingPlan ((hausdorff n X).restrict (closedBall p (3*R)))
      ν₀ ν₁ π midpointTime q) :
    π.map (fun γ => γ midpointTime) ≪ (hausdorff n X).restrict (closedBall p (3*R)) := by
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3*R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3*R)) isBounded_closedBall⟩
  let ν := π.map (fun γ => γ midpointTime)
  change ν ≪ μ
  by_contra hnot
  have hξ : ν.singularPart μ ≠ 0 := fun hz => hnot ((Measure.singularPart_eq_zero ν μ).mp hz)
  obtain ⟨S,hS,hμS,hξSc⟩ := (Measure.mutuallySingular_singularPart ν μ).symm
  have hrestrict : ν.singularPart μ = ν.restrict S := Measure.singularPart_eq_restrict hξSc hμS
  have hνS : ν S ≠ 0 := by
    intro hz
    apply hξ
    rw [hrestrict]
    exact Measure.restrict_eq_zero.mpr hz
  obtain ⟨σ,hσ,hgσ,hpσ,hmσ,hcapσ⟩ := hX.compressed_replacement_subplan K n hn
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 π hg hp S hS hνS
  let := hσ
  let η := σ.map (fun γ => γ midpointTime)
  have hη : η ≪ μ := Measure.absolutelyContinuous_of_le_smul hcapσ
  have hηpos : 0 < η univ := by
    rw [show η univ=ν S from hmσ]
    exact pos_iff_ne_zero.mpr hνS
  have hstrict := renyi_singular_replacement_strict μ ν η hη hηpos hq0 hq1
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' S)
  have hκ : κ ≤ π := Measure.restrict_le_self
  obtain ⟨hprob,hgeo,hopt⟩ := optimalPlan_replace_subplan hp hg hκ hpσ hgσ
  have hle := hmax (π-κ+σ) hprob hgeo hopt
  have hκmid : κ.map (fun γ => γ midpointTime) = ν.restrict S :=
    (Measure.restrict_map (measurable_path_eval midpointTime) hS).symm
  have hnew : (π-κ+σ).map (fun γ => γ midpointTime) = ν-ν.singularPart μ+η := by
    rw [Measure.map_add _ _ (measurable_path_eval midpointTime),
      map_sub_of_le π κ hκ _ (measurable_path_eval midpointTime),hκmid,hrestrict]
  change (∫ x, (((π-κ+σ).map (fun γ => γ midpointTime)).rnDeriv μ x).toReal^q ∂μ) ≤
    ∫ x, (ν.rnDeriv μ x).toReal^q ∂μ at hle
  rw [hnew] at hle
  exact (not_lt_of_ge hle) hstrict

end RegularPointCoordinates

end

end OAI
