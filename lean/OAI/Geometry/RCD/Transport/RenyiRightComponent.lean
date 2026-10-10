import OAI.Geometry.RCD.Transport.OptimalRightSplice
import OAI.Geometry.RCD.Transport.SubpathMeasureSub
import OAI.Geometry.RCD.Transport.LengthReplacementSeparation
import OAI.Geometry.RCD.Coordinates.RenyiNormalizedComparison

namespace OAI

/-! # Maximality of a length component on the right half

A competing half-plan is spliced into the full transport while keeping the
original midpoint. The common length labels then give the disjointness
needed to transfer midpoint maximality to the normalized component.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.renyi_right_length_component_maximal
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0≤R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p≤R) (hs1 : ∀ᵐ x ∂ν₁, dist x p≤R)
    (μ : Measure X) [IsFiniteMeasure μ]
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ : Measure C(Time,X)) (hκeq : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (hκ0 : κ univ≠0) {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan μ (π.map (fun γ => γ midpointTime)) (π.map (fun γ => γ 1))
      (π.map (subpath midpointTime 1)) midpointTime q) :
    RenyiMaximizingPlan μ ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1))
      ((κ univ)⁻¹ • κ.map (subpath midpointTime 1)) midpointTime q := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨p⟩
  have hA : MeasurableSet {γ : C(Time,X) | dist (γ 0) (γ 1)∈S} :=
    hS.preimage ((measurable_path_eval 0).dist (measurable_path_eval 1))
  have hκ : κ≤π := by rw [hκeq]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have he := optimalPlan_endpoints ν₀ ν₁ π hpπ
  have hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hpπ
  have hfin := finite_second_moment_cost (finiteSecondMoment_of_bounded ν₀ p hs0)
    (finiteSecondMoment_of_bounded ν₁ p hs1) hpπ.1 hpπ.2.1
  let πR := π.map (subpath midpointTime 1)
  let κR := κ.map (subpath midpointTime 1)
  have hκR : κR≤πR := Measure.map_mono hκ (subpath_measurable midpointTime 1)
  have hcK : κR univ=κ univ := by
    simp only [κR,Measure.map_apply (subpath_measurable midpointTime 1) MeasurableSet.univ,preimage_univ]
  obtain ⟨hπR,hgL,hpL⟩ := geodesic_subpath_law π hgπ hp hfin midpointTime 1
  let : IsProbabilityMeasure πR := hπR
  have heK (s : Time) : κR.map (fun γ => γ s)=κ.map (fun γ => γ (upperTime s)) :=
    subpath_map_eval κ midpointTime 1 s
  have hresid : (πR-κR).map (fun γ => γ midpointTime)=
      (π-κ).map (fun γ => γ (upperTime midpointTime)) := by
    change (π.map (subpath midpointTime 1)-κ.map (subpath midpointTime 1)).map _=_
    rw [←subpath_map_sub π κ hκ midpointTime 1]
    exact subpath_map_eval (π-κ) midpointTime 1 midpointTime
  have hu0 : 0<(upperTime midpointTime:ℝ) := by norm_num [coe_upperTime,midpointTime]
  have hu1 : (upperTime midpointTime:ℝ)<1 := by norm_num [coe_upperTime,midpointTime]
  have hκS : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)∈S := by rw [hκeq]; exact ae_restrict_mem hA
  have hresS : ∀ᵐ γ ∂π-κ, dist (γ 0) (γ 1)∉S := by
    apply ae_iff.mpr
    simp only [not_not]
    rw [Measure.sub_apply hA hκ,hκeq,Measure.restrict_apply hA,inter_self,tsub_self]
  have hsκ : (πR-κR).map (fun γ => γ midpointTime) ⟂ₘ κR.map (fun γ => γ midpointTime) := by
    rw [hresid,heK]
    exact (hX.optimal_components_mutuallySingular K n hn ν₀ ν₁ hac p hR hs0 hs1
      π π hgπ hgπ hpπ hpπ κ (π-κ) hκ Measure.sub_le hu0 hu1 hS hκS hresS).symm
  intro σ hσ hgσ hpσ
  let := hσ
  obtain ⟨τ,hτ,hgτ,hpτ,hl,hr⟩ := exists_optimal_right_subplan_splice π hgπ hp hfin κ hκ hκ0 σ hgσ hpσ
  have hmid : κ.map (fun γ => γ midpointTime)=τ.map (fun γ => γ midpointTime) := by
    simpa only [lowerTime,timeSegment_one] using (hr 1).symm
  have hsep := hX.length_replacement_separated K n hn ν₀ ν₁ hac p hR hs0 hs1 π hgπ hpπ
    hS κ τ hκeq hpτ hgτ (by norm_num [midpointTime]) (by norm_num [midpointTime]) hmid hu0 hu1
  rw [←hresid,hl] at hsep
  have hsσ : (πR-κR).map (fun γ => γ midpointTime) ⟂ₘ σ.map (fun γ => γ midpointTime) :=
    hsep.mono_ac Measure.AbsolutelyContinuous.rfl (Measure.absolutelyContinuous_smul hκ0)
  have hpσL : IsOptimalCoupling ((κR univ)⁻¹ • κR.map (fun γ => γ 0))
      ((κR univ)⁻¹ • κR.map (fun γ => γ 1)) (σ.map (fun γ => (γ 0,γ 1))) := by
    simpa only [hcK,heK,upperTime,timeSegment_zero,timeSegment_one] using hpσ
  have hh := hmax.normalized_subplan_comparison μ hq0 hq1 hgL hpL hκR
    (hcK ▸ hκ0) hpσL hgσ hsκ hsσ
  simpa only [hcK,Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable] using hh

end RegularPointCoordinates

end

end OAI
