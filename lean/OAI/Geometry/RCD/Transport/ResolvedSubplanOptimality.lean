import OAI.Geometry.RCD.Transport.ResolvedPairAgreement
import OAI.Geometry.RCD.Transport.EndpointDominatedOptimality

namespace OAI

/-! # Actual normalized optimal laws after resolving a paired subplan -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem normalized_resolved_subplan_optimal
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1))) ≠ ∞)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π) (q : Time) :
    let ρ := (σ univ)⁻¹ • σ
    let τ := ρ.map (resolvePathBranch q)
    IsProbabilityMeasure τ ∧ (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling (τ.map (fun γ => γ 0)) (τ.map (fun γ => γ 1))
        (τ.map (fun γ => (γ 0,γ 1))) := by
  let : NeZero σ := ⟨by intro he; apply hσ; rw [he]; rfl⟩
  let ρ := (σ univ)⁻¹ • σ
  let : IsProbabilityMeasure ρ := inferInstance
  let τ := ρ.map (resolvePathBranch q)
  have hg₀ : ∀ᵐ z ∂σ, IsGeodesic z.1 :=
    (ae_map_iff measurable_fst.aemeasurable isClosed_geodesicSet.measurableSet).mp
      (hg.filter_mono hl.absolutelyContinuous.ae_le)
  have hg₁ : ∀ᵐ z ∂σ, IsGeodesic z.2 :=
    (ae_map_iff measurable_snd.aemeasurable isClosed_geodesicSet.measurableSet).mp
      (hg.filter_mono hr.absolutelyContinuous.ae_le)
  have hρg : ∀ᵐ z ∂ρ, IsGeodesic z.1 ∧ IsGeodesic z.2 :=
    (hg₀.and hg₁).filter_mono Measure.smul_absolutelyContinuous.ae_le
  refine ⟨inferInstance,resolved_branch_geodesic q ρ hρg,?_⟩
  have hm := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
  have hdom : σ.map (fun z => (z.2 0,z.2 1)) ≤ π.map (fun γ => (γ 0,γ 1)) := by
    simpa only [Measure.map_map hm measurable_snd,Function.comp_def] using Measure.map_mono hr hm
  apply optimal_of_endpoint_domination π τ hp hfin
    (ENNReal.inv_ne_zero.mpr (measure_ne_top σ univ)) (ENNReal.inv_ne_top.mpr hσ)
  rw [resolved_branch_endpoints q ρ,Measure.map_map hm measurable_snd]
  change ((σ univ)⁻¹ • σ).map (fun z => (z.2 0,z.2 1)) ≤ _
  have hm' : Measurable (fun z : C(Time,X)×C(Time,X) => (z.2 0,z.2 1)) :=
    hm.comp measurable_snd
  rw [Measure.map_smul _ hm'.aemeasurable]
  intro B
  exact mul_le_mul' le_rfl (hdom B)

end RegularPointCoordinates

end

end OAI
