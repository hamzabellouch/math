import OAI.Geometry.RCD.Transport.MeetingSplice

namespace OAI

/-! # Splicing a conditional pair preserves the actual optimal cost -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem meeting_splice_optimal (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsProbabilityMeasure σ]
    (hl : σ.map Prod.fst=π) (hr : σ.map Prod.snd=π)
    (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (hmeet : ∀ᵐ z ∂σ, z.1 t=z.2 t) :
    let τ := σ.map (meetingSplice t)
    (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      τ.map (fun γ => γ 0)=π.map (fun γ => γ 0) ∧
      τ.map (fun γ => γ 1)=π.map (fun γ => γ 1) ∧
      IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (τ.map (fun γ => (γ 0,γ 1))) := by
  have hcset : MeasurableSet {γ : C(Time,X) | φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2} :=
    measurableSet_eq_fun ((hφ.comp (measurable_path_eval 0)).add (hψ.comp (measurable_path_eval 1)))
      ((((measurable_path_eval 0).dist (measurable_path_eval 1)).pow_const 2).div_const 2)
  have hg₀ : ∀ᵐ z ∂σ, IsGeodesic z.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable isClosed_geodesicSet.measurableSet).mp
    rwa [hl]
  have hg₁ : ∀ᵐ z ∂σ, IsGeodesic z.2 := by
    apply (ae_map_iff measurable_snd.aemeasurable isClosed_geodesicSet.measurableSet).mp
    rwa [hr]
  have hc₀ : ∀ᵐ z ∂σ, φ (z.1 0)+ψ (z.1 1)=dist (z.1 0) (z.1 1)^2/2 := by
    apply (ae_map_iff measurable_fst.aemeasurable hcset).mp
    rwa [hl]
  have hc₁ : ∀ᵐ z ∂σ, φ (z.2 0)+ψ (z.2 1)=dist (z.2 0) (z.2 1)^2/2 := by
    apply (ae_map_iff measurable_snd.aemeasurable hcset).mp
    rwa [hr]
  let τ := σ.map (meetingSplice t)
  have hτ₀ : τ.map (fun γ => γ 0)=π.map (fun γ => γ 0) := by
    rw [←hl,Measure.map_map (measurable_path_eval 0) measurable_fst,
      Measure.map_map (measurable_path_eval 0) (measurable_meetingSplice t)]
    apply Measure.map_congr
    exact .of_forall fun z => meetingSplice_left t z t.property.1
  have hτ₁ : τ.map (fun γ => γ 1)=π.map (fun γ => γ 1) := by
    rw [←hr,Measure.map_map (measurable_path_eval 1) measurable_snd,
      Measure.map_map (measurable_path_eval 1) (measurable_meetingSplice t)]
    apply Measure.map_congr
    exact hmeet.mono fun z hz => meetingSplice_right t z hz t.property.2
  have hcost : transportCost (τ.map (fun γ => (γ 0,γ 1)))=
      transportCost (π.map (fun γ => (γ 0,γ 1))) := by
    have hm := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
    have hdist : Measurable (fun z : X×X => ENNReal.ofReal (dist z.1 z.2)^2) :=
      ((measurable_fst.dist measurable_snd).ennreal_ofReal).pow_const 2
    have hpath : Measurable (fun γ : C(Time,X) => ENNReal.ofReal (dist (γ 0) (γ 1))^2) :=
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).ennreal_ofReal).pow_const 2
    unfold transportCost
    simp_rw [lintegral_map hdist hm]
    rw [←hl,lintegral_map hpath measurable_fst]
    change (∫⁻ γ, ENNReal.ofReal (dist (γ 0) (γ 1))^2 ∂σ.map (meetingSplice t))=_
    rw [lintegral_map hpath (measurable_meetingSplice t)]
    apply lintegral_congr_ae
    filter_upwards [hg₀,hg₁,hc₀,hc₁,hmeet] with z hz₀ hz₁ hc₀ hc₁ hz
    rw [meetingSplice_left t z t.property.1,meetingSplice_right t z hz t.property.2,
      (contacting_geodesics_cross_length had hz₀ hz₁ hc₀ hc₁ ht0 ht1 hz).1]
  refine ⟨?_,hτ₀,hτ₁,?_,?_,?_⟩
  · apply (ae_map_iff (measurable_meetingSplice t).aemeasurable isClosed_geodesicSet.measurableSet).mpr
    filter_upwards [hg₀,hg₁,hc₀,hc₁,hmeet] with z hz₀ hz₁ hc₀ hc₁ hz
    simpa only [meetingSplice,dite_eq_left hz] using contacting_splice_isGeodesic had hz₀ hz₁ hc₀ hc₁ ht0 ht1 hz
  · simpa only [Measure.map_map measurable_fst
      ((measurable_path_eval 0).prodMk (measurable_path_eval 1)),Function.comp_def] using hτ₀
  · simpa only [Measure.map_map measurable_snd
      ((measurable_path_eval 0).prodMk (measurable_path_eval 1)),Function.comp_def] using hτ₁
  · intro η hη₀ hη₁
    rw [hcost]
    exact hp.2.2 η hη₀ hη₁

end RegularPointCoordinates

end

end OAI
