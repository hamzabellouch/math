import OAI.Geometry.RCD.Transport.OptimalInitialSubmeasure
import OAI.Geometry.RCD.Coordinates.RenyiNormalizedComparison
import OAI.Geometry.RCD.Transport.OptimalComponentSeparation

namespace OAI

/-! # Maximality of an entire length component

The initial speed identity ensures that any optimal replacement stays in
the same length class. Its interior mass is disjoint from the untouched
class, so exact Rényi additivity transfers maximality to the component.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.renyi_root_length_component_maximal
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (μ : Measure X) [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ : Measure C(Time,X)) (hκeq : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (hκ0 : κ univ≠0) {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hmax : RenyiMaximizingPlan μ a.left a.right π midpointTime q) :
    RenyiMaximizingPlan μ ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1)) ((κ univ)⁻¹ • κ) midpointTime q := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  have hκ : κ≤π := by rw [hκeq]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hκtop : κ univ≠∞ := measure_ne_top κ univ
  have hA : MeasurableSet {γ : C(Time,X) | dist (γ 0) (γ 1)∈S} :=
    hS.preimage ((measurable_path_eval 0).dist (measurable_path_eval 1))
  have hκS : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)∈S := by rw [hκeq]; exact ae_restrict_mem hA
  have hres : ∀ᵐ γ ∂π-κ, dist (γ 0) (γ 1)∉S := by
    apply ae_iff.mpr
    simp only [not_not]
    rw [Measure.sub_apply hA hκ,hκeq,Measure.restrict_apply hA,inter_self,tsub_self]
  have hac : a.left ≪ hausdorff n X := Measure.absolutelyContinuous_of_le_smul a.left_bound
  have hsκ := (hX.optimal_components_mutuallySingular K n hn a.left a.right hac
    a.center a.radius_nonneg a.left_support a.right_support π π hg hg hp hp
    κ (π-κ) hκ Measure.sub_le (t:=midpointTime) (by norm_num [midpointTime])
    (by norm_num [midpointTime]) hS hκS hres).symm
  intro σ hσ hgσ hpσ
  let := hσ
  let τ := κ univ • σ
  have hτ : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (τ.map (fun γ => (γ 0,γ 1))) := by
    have hh := hpσ.smul hκ0 hκtop
    simpa only [τ,Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable,
      smul_smul,ENNReal.mul_inv_cancel hκ0 hκtop,one_smul] using hh
  have hgτ : ∀ᵐ γ ∂τ, IsGeodesic γ := hgσ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hρ,hgρ,hpρ⟩ := optimalPlan_replace_subplan hp hg hκ hτ hgτ
  let ρ := π-κ+τ
  let : IsProbabilityMeasure ρ := hρ
  have hτle : τ≤ρ := Measure.le_add_left le_rfl
  have hτS := hX.optimal_initial_submeasure_length_transfer K n hn a π ρ hg hgρ hp hpρ
    hC hc κ τ hκ hτle (optimalPlan_endpoints _ _ τ hτ).1.symm hS hκS
  have hsτ := (hX.optimal_components_mutuallySingular K n hn a.left a.right hac
    a.center a.radius_nonneg a.left_support a.right_support ρ π hgρ hg hpρ hp
    τ (π-κ) hτle Measure.sub_le (t:=midpointTime) (by norm_num [midpointTime])
    (by norm_num [midpointTime]) hS hτS hres).symm
  have hsσ : (π-κ).map (fun γ => γ midpointTime) ⟂ₘ σ.map (fun γ => γ midpointTime) := by
    rw [show τ.map (fun γ => γ midpointTime)=κ univ • σ.map (fun γ => γ midpointTime) from
      Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable] at hsτ
    exact hsτ.mono_ac Measure.AbsolutelyContinuous.rfl (Measure.absolutelyContinuous_smul hκ0)
  simpa only [Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable] using
    hmax.normalized_subplan_comparison μ hq0 hq1 hg hp hκ hκ0 hpσ hgσ hsκ hsσ

end RegularPointCoordinates

end

end OAI
