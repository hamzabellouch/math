import OAI.Geometry.RCD.Transport.OptimalExactSplice
import OAI.Geometry.RCD.Coordinates.NormalizedOptimalSubplan
import OAI.Geometry.RCD.Transport.OptimalSubmeasureLength
import OAI.Geometry.RCD.Transport.RenyiTransportNode

namespace OAI

/-! # Sharp half-distance bounds for a bounded-length component

Every optimal replacement of either half stays below half the component's
length bound. The proof splices it into the parent transport and uses the
common interior length label at the retained midpoint.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.component_splice_distance
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0)
    {D : ℝ} (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D)
    (q₀ q₁ : Measure C(Time,X)) [IsProbabilityMeasure q₀] [IsProbabilityMeasure q₁]
    (hg₀ : ∀ᵐ γ ∂q₀, IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂q₁, IsGeodesic γ)
    (hp₀ : IsOptimalCoupling ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime)) (q₀.map (fun γ => (γ 0,γ 1))))
    (hp₁ : IsOptimalCoupling ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime))
      ((κ univ)⁻¹ • κ.map (fun γ => γ 1)) (q₁.map (fun γ => (γ 0,γ 1)))) :
    (∀ᵐ γ ∂q₀, dist (γ 0) (γ 1)≤D/2) ∧
      ∀ᵐ γ ∂q₁, dist (γ 0) (γ 1)≤D/2 := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨a.center⟩
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hc : κ univ≠∞ := measure_ne_top κ univ
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,hfn⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  have hp₀' : IsOptimalCoupling (πn.map (fun γ => γ 0)) (πn.map (fun γ => γ midpointTime))
      (q₀.map (fun γ => (γ 0,γ 1))) := by rwa [heval,heval]
  have hp₁' : IsOptimalCoupling (πn.map (fun γ => γ midpointTime)) (πn.map (fun γ => γ 1))
      (q₁.map (fun γ => (γ 0,γ 1))) := by rwa [heval,heval]
  obtain ⟨τ,hτ,hgτ,hpτ,hl,hr⟩ := exists_optimal_midpoint_splice_exact πn hgn hpn hfn
    q₀ q₁ hg₀ hg₁ hp₀' hp₁'
  let := hτ
  let ζ := κ univ • τ
  have hgζ : ∀ᵐ γ ∂ζ, IsGeodesic γ := hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hpζ : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (ζ.map (fun γ => (γ 0,γ 1))) := by
    have hh := hpτ.smul hκ0 hc
    rw [heval,heval,smul_smul,smul_smul,ENNReal.mul_inv_cancel hκ0 hc,one_smul,one_smul] at hh
    simpa only [ζ,Measure.map_smul _ ((measurable_path_eval 0).prodMk
      (measurable_path_eval 1)).aemeasurable] using hh
  have hmid : κ.map (fun γ => γ midpointTime)=ζ.map (fun γ => γ midpointTime) := by
    have hmidτ : τ.map (fun γ => γ midpointTime)=q₀.map (fun γ => γ 1) := by
      have hh := subpath_map_eval τ 0 midpointTime 1
      simpa only [hl,timeSegment_one] using hh.symm
    dsimp only [ζ]
    rw [Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable,
      hmidτ,(optimalPlan_endpoints _ _ q₀ hp₀).2,smul_smul,
      ENNReal.mul_inv_cancel hκ0 hc,one_smul]
  obtain ⟨hρ,hgρ,hpρ⟩ := optimalPlan_replace_subplan hp hg hκ hpζ hgζ
  let ρ := π-κ+ζ
  let : IsProbabilityMeasure ρ := hρ
  have hζ : ζ≤ρ := Measure.le_add_left le_rfl
  have hζD := hX.optimal_submeasure_length_transfer K n hn a.left a.right
    (Measure.absolutelyContinuous_of_le_smul a.left_bound) a.center a.radius_nonneg
    a.left_support a.right_support π ρ hg hgρ hp hpρ κ ζ hκ hζ
    (by norm_num [midpointTime]) (by norm_num [midpointTime]) hmid measurableSet_Iic hD
  have hτD : ∀ᵐ γ ∂τ, dist (γ 0) (γ 1)≤D :=
    hζD.filter_mono (Measure.absolutelyContinuous_smul hκ0).ae_le
  have hhalf : ∀ᵐ γ ∂τ, dist (γ 0) (γ midpointTime)≤D/2 ∧
      dist (γ midpointTime) (γ 1)≤D/2 := by
    filter_upwards [hgτ,hτD] with γ hγ hγD
    rw [hγ 0 midpointTime,hγ midpointTime 1]
    norm_num [midpointTime]
    linarith
  constructor
  · rw [←hl]
    apply (ae_map_iff (subpath_measurable 0 midpointTime).aemeasurable
      (measurableSet_le ((measurable_path_eval 0).dist (measurable_path_eval 1)) measurable_const)).mpr
    simpa only [subpath_zero,subpath_one] using hhalf.mono (fun _ h => h.1)
  · rw [←hr]
    apply (ae_map_iff (subpath_measurable midpointTime 1).aemeasurable
      (measurableSet_le ((measurable_path_eval 0).dist (measurable_path_eval 1)) measurable_const)).mpr
    simpa only [subpath_zero,subpath_one] using hhalf.mono (fun _ h => h.2)

end RegularPointCoordinates

end

end OAI
