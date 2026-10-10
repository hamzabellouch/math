import OAI.Geometry.RCD.Transport.GlobalLengthRootMaximality
import OAI.Geometry.RCD.Transport.CompressedPlanChildren
import OAI.Geometry.RCD.Transport.LengthRestrictionSubpath

namespace OAI

/-! # Whole length components inherit all dyadic maximality

Half-subpath restriction rescales the length label. The endpoint speed
identity therefore transfers every level of the actual variational tree.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.length_component_dyadic_maximal
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {C : ℝ≥0∞} (hC : C≠∞) (m : ℕ) :
    ∀ (a : RenyiTransportNode n X) (π : Measure C(Time,X)) (_hπ : IsProbabilityMeasure π),
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) →
      (∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X) →
      RenyiDyadicMaximal (hausdorff n X) q (fun t => π.map (fun γ => γ t)) m →
      ∀ (S : Set ℝ), MeasurableSet S → ∀ κ : Measure C(Time,X),
        κ=π.restrict {γ | dist (γ 0) (γ 1)∈S} → κ univ≠0 →
        RenyiDyadicMaximal (hausdorff n X) q
          (fun t => ((κ univ)⁻¹ • κ).map (fun γ => γ t)) m := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  induction m with
  | zero => intro a π hπ hg hp hc hm S hS κ heκ hκ0; trivial
  | succ m ih =>
    intro a π hπ hg hp hc hm S hS κ heκ hκ0
    let := hπ
    let : Nonempty X := ⟨a.center⟩
    let := a.left_probability
    let := a.right_probability
    have he := optimalPlan_endpoints a.left a.right π hp
    have hr := hm.1
    dsimp only at hr
    rw [he.1,he.2] at hr
    have hroot := hX.global_root_length_component K n hn a π hg hp hC hc hS κ heκ hκ0 hq0 hq1 hr
    obtain ⟨a₀,a₁,h00,h0m,h1m,h11,_,_⟩ := compressed_plan_children a π hg hp hC hc
    have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
    have hfin := finite_second_moment_cost
      (finiteSecondMoment_of_bounded a.left a.center a.left_support)
      (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
    obtain ⟨hL,hgL,hpL⟩ := geodesic_subpath_law π hg hpp hfin 0 midpointTime
    obtain ⟨hR,hgR,hpR⟩ := geodesic_subpath_law π hg hpp hfin midpointTime 1
    have hpL' : IsOptimalCoupling a₀.left a₀.right
        ((π.map (subpath 0 midpointTime)).map (fun γ => (γ 0,γ 1))) := by rw [h00,h0m]; exact hpL
    have hpR' : IsOptimalCoupling a₁.left a₁.right
        ((π.map (subpath midpointTime 1)).map (fun γ => (γ 0,γ 1))) := by rw [h1m,h11]; exact hpR
    have hcL (t : Time) : (π.map (subpath 0 midpointTime)).map (fun γ => γ t)≤C • hausdorff n X := by
      rw [subpath_map_eval]; exact hc _
    have hcR (t : Time) : (π.map (subpath midpointTime 1)).map (fun γ => γ t)≤C • hausdorff n X := by
      rw [subpath_map_eval]; exact hc _
    have hmL := hm.2.1.congr (fun t => (subpath_map_eval π 0 midpointTime t).symm)
    have hmR := hm.2.2.congr (fun t => (subpath_map_eval π midpointTime 1 t).symm)
    let T := (fun d : ℝ => 2*d) ⁻¹' S
    have hT : MeasurableSet T := hS.preimage (measurable_const.mul measurable_id)
    have hκL : κ.map (subpath 0 midpointTime)=
        (π.map (subpath 0 midpointTime)).restrict {γ | dist (γ 0) (γ 1)∈T} := by
      rw [heκ]
      exact length_restriction_subpath π hg 0 midpointTime (by norm_num [midpointTime]) hS
    have hκR : κ.map (subpath midpointTime 1)=
        (π.map (subpath midpointTime 1)).restrict {γ | dist (γ 0) (γ 1)∈T} := by
      rw [heκ]
      exact length_restriction_subpath π hg midpointTime 1 (by norm_num [midpointTime]) hS
    have hmass (s t : Time) : (κ.map (subpath s t)) univ=κ univ := by
      rw [Measure.map_apply (subpath_measurable s t) MeasurableSet.univ,preimage_univ]
    have hiL := ih a₀ _ hL hgL hpL' hcL hmL T hT _ hκL (by rwa [hmass])
    have hiR := ih a₁ _ hR hgR hpR' hcR hmR T hT _ hκR (by rwa [hmass])
    have heval (s t r : Time) :
        (((κ.map (subpath s t)) univ)⁻¹ • κ.map (subpath s t)).map (fun γ => γ r)=
          ((κ univ)⁻¹ • κ).map (fun γ => γ (timeSegment s t r)) := by
      rw [Measure.map_smul _ (measurable_path_eval r).aemeasurable,hmass,subpath_map_eval,
        Measure.map_smul _ (measurable_path_eval _).aemeasurable]
    refine ⟨?_,hiL.congr (fun t => heval 0 midpointTime t),
      hiR.congr (fun t => heval midpointTime 1 t)⟩
    simpa only [RenyiMidpointMaximal,RenyiMaximizingPlan,
      Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable] using hroot

end RegularPointCoordinates

end

end OAI
