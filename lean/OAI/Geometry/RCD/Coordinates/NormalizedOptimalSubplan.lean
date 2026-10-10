import OAI.Geometry.RCD.Transport.OptimalMidpointSplice

namespace OAI

/-! # Normalizing a nonzero component of an optimal geodesic plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem normalized_optimal_subplan
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1)))≠∞)
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0) :
    let πn := (κ univ)⁻¹ • κ
    IsProbabilityMeasure πn ∧ (∀ᵐ γ ∂πn, IsGeodesic γ) ∧
      IsOptimalCoupling (πn.map (fun γ => γ 0)) (πn.map (fun γ => γ 1))
        (πn.map (fun γ => (γ 0,γ 1))) ∧
      transportCost (πn.map (fun γ => (γ 0,γ 1)))≠∞ := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  let : NeZero κ := ⟨by intro he; apply hκ0; rw [he]; rfl⟩
  have hc : κ univ≠∞ := measure_ne_top κ univ
  have hi0 : (κ univ)⁻¹≠0 := ENNReal.inv_ne_zero.mpr hc
  have hit : (κ univ)⁻¹≠∞ := ENNReal.inv_ne_top.mpr hκ0
  let πn := (κ univ)⁻¹ • κ
  have hm := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
  have hle := Measure.map_mono hκ hm
  have hcost : transportCost (κ.map (fun γ => (γ 0,γ 1)))≠∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono' hle le_rfl)
  have hoptκ : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (κ.map (fun γ => (γ 0,γ 1))) := by
    simpa only [Measure.map_map measurable_fst hm,Measure.map_map measurable_snd hm,Function.comp_def]
      using hp.subcoupling hfin hle
  refine ⟨inferInstance,?_,?_,?_⟩
  · exact (hg.filter_mono hκ.absolutelyContinuous.ae_le).filter_mono Measure.smul_absolutelyContinuous.ae_le
  · rw [Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable,Measure.map_smul _ hm.aemeasurable]
    exact hoptκ.smul hi0 hit
  · rw [Measure.map_smul _ hm.aemeasurable,transportCost_smul]
    exact ENNReal.mul_ne_top hit hcost

end RegularPointCoordinates

end

end OAI
