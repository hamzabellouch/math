import OAI.Geometry.RCD.Sobolev.WeightedMatchedJoin
import OAI.Geometry.RCD.Harmonic.WeightedQuadraticGluing
import OAI.Geometry.RCD.Transport.TripletTransportCost

namespace OAI

/-! # Optimal completion of a geodesic triplet law by matched path laws -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {A X : Type*} [MeasurableSpace A] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem weighted_matched_law_optimal
    (P : Measure A) (x a b : A → X) (hx : Measurable x) (ha : Measurable a) (hb : Measurable b)
    (t : Ioo (0:ℝ) 1)
    (hp : IsOptimalCoupling (P.map a) (P.map b) (P.map (fun z => (a z,b z))))
    (hfin : transportCost (P.map (fun z => (a z,b z))) ≠ ∞)
    (hgeo : ∀ᵐ z ∂P, dist (x z) (a z)=(t:ℝ)*dist (a z) (b z) ∧
      dist (x z) (b z)=(1-(t:ℝ))*dist (a z) (b z))
    (q₀ q₁ : Measure C(Time,X))
    (hg₀ : ∀ᵐ γ ∂q₀, IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂q₁, IsGeodesic γ)
    (hp₀ : IsOptimalCoupling (P.map a) (P.map x) (q₀.map (fun γ => (γ 0,γ 1))))
    (hp₁ : IsOptimalCoupling (P.map x) (P.map b) (q₁.map (fun γ => (γ 0,γ 1))))
    (ρ : Measure (MatchedPaths X))
    (hρ₀ : ρ.map (fun z => z.val.1)=q₀) (hρ₁ : ρ.map (fun z => z.val.2)=q₁) :
    IsOptimalCoupling (P.map a) (P.map b)
      ((ρ.map (weightedJoin t)).map (fun γ => (γ 0,γ 1))) ∧
      (∀ᵐ γ ∂ρ.map (weightedJoin t), IsGeodesic γ) := by
  let C := transportCost (P.map (fun z => (a z,b z)))
  let l := fun z : MatchedPaths X => dist (z.val.1 0) (z.val.1 1)
  let r := fun z : MatchedPaths X => dist (z.val.2 0) (z.val.2 1)
  let d := fun z : MatchedPaths X => dist (z.val.1 0) (z.val.2 1)
  have he₀ := optimalPlan_endpoints _ _ q₀ hp₀
  have he₁ := optimalPlan_endpoints _ _ q₁ hp₁
  have hends₀ : ((ρ.map (weightedJoin t)).map (fun γ => (γ 0,γ 1))).map Prod.fst=P.map a := by
    rw [Measure.map_map measurable_fst ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    exact (weightedJoin_law_zero t ρ q₀ hρ₀).trans he₀.1
  have hends₁ : ((ρ.map (weightedJoin t)).map (fun γ => (γ 0,γ 1))).map Prod.snd=P.map b := by
    rw [Measure.map_map measurable_snd ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    exact (weightedJoin_law_one t ρ q₁ hρ₁).trans he₁.2
  have hl : Measurable l := ((measurable_path_eval 0).comp measurable_subtype_coe.fst).dist
    ((measurable_path_eval 1).comp measurable_subtype_coe.fst)
  have hr : Measurable r := ((measurable_path_eval 0).comp measurable_subtype_coe.snd).dist
    ((measurable_path_eval 1).comp measurable_subtype_coe.snd)
  have hlCost : ∫⁻ z, ENNReal.ofReal (l z)^2 ∂ρ=
      transportCost (q₀.map (fun γ => (γ 0,γ 1))) := by
    rw [transportCost_plan_lintegral,← hρ₀,lintegral_map
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)
      measurable_subtype_coe.fst]
  have hrCost : ∫⁻ z, ENNReal.ofReal (r z)^2 ∂ρ=
      transportCost (q₁.map (fun γ => (γ 0,γ 1))) := by
    rw [transportCost_plan_lintegral,← hρ₁,lintegral_map
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)
      measurable_subtype_coe.snd]
  have hdCost : ∫⁻ z, ENNReal.ofReal (d z)^2 ∂ρ=
      transportCost ((ρ.map (weightedJoin t)).map (fun γ => (γ 0,γ 1))) := by
    rw [transportCost_plan_lintegral,lintegral_map
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal.pow_const 2)
      (weightedJoin_continuous t).measurable]
    simp only [weightedJoin_zero,weightedJoin_one,d]
  have h0 : ∫⁻ z, ENNReal.ofReal (l z)^2 ∂ρ ≤ ENNReal.ofReal (t:ℝ)^2*C := by
    rw [hlCost]
    have hs := transportCost_map_scale P ha hx ha hb t.property.1.le
      (hgeo.mono fun z hz => (dist_comm (a z) (x z)).trans hz.1)
    rw [← hs]
    exact hp₀.2.2 _ (by rw [Measure.map_map measurable_fst (ha.prodMk hx)]; rfl)
      (by rw [Measure.map_map measurable_snd (ha.prodMk hx)]; rfl)
  have h1 : ∫⁻ z, ENNReal.ofReal (r z)^2 ∂ρ ≤ ENNReal.ofReal (1-(t:ℝ))^2*C := by
    rw [hrCost]
    have hs := transportCost_map_scale P hx hb ha hb (sub_pos.mpr t.property.2).le
      (hgeo.mono fun _ hz => hz.2)
    rw [← hs]
    exact hp₁.2.2 _ (by rw [Measure.map_map measurable_fst (hx.prodMk hb)]; rfl)
      (by rw [Measure.map_map measurable_snd (hx.prodMk hb)]; rfl)
  have htri (z : MatchedPaths X) : d z ≤ l z+r z := by
    dsimp only [d,l,r]
    rw [← z.property]
    exact dist_triangle _ _ _
  obtain ⟨hcost,heq⟩ := weighted_quadratic_gluing_saturation ρ l r d hl hr
    (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall fun _ => dist_nonneg)
    (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall htri)
    t.property.1 t.property.2 C hfin h0 h1
    (by rw [hdCost]; exact hp.2.2 _ hends₀ hends₁)
  refine ⟨⟨hends₀,hends₁,?_⟩,?_⟩
  · intro κ hk₀ hk₁
    rw [← hdCost,hcost]
    exact hp.2.2 κ hk₀ hk₁
  · apply (ae_map_iff (weightedJoin_continuous t).measurable.aemeasurable
      isClosed_geodesicSet.measurableSet).mpr
    have hgeo₀ : ∀ᵐ z ∂ρ, IsGeodesic z.val.1 :=
      ae_of_ae_map measurable_subtype_coe.fst.aemeasurable (hρ₀ ▸ hg₀)
    have hgeo₁ : ∀ᵐ z ∂ρ, IsGeodesic z.val.2 :=
      ae_of_ae_map measurable_subtype_coe.snd.aemeasurable (hρ₁ ▸ hg₁)
    filter_upwards [hgeo₀,hgeo₁,heq] with z hz₀ hz₁ hz
    exact weightedJoin_isGeodesic t z hz₀ hz₁ hz.1 hz.2

end RegularPointCoordinates

end

end OAI
