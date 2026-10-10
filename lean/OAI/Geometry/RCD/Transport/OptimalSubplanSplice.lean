import OAI.Geometry.RCD.Coordinates.NormalizedOptimalSubplan

namespace OAI

/-! # Splicing an actual subplan through its fixed interior marginal

A normalized half-plan is lifted back to the original component mass.
Both outside endpoint marginals and the entire untouched half are retained.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [Nonempty X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_optimal_left_subplan_splice
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1)))≠∞)
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0)
    (q : Measure C(Time,X)) [IsProbabilityMeasure q]
    (hgq : ∀ᵐ γ ∂q, IsGeodesic γ)
    (hpq : IsOptimalCoupling ((κ univ)⁻¹ • κ.map (fun γ => γ 0))
      ((κ univ)⁻¹ • κ.map (fun γ => γ midpointTime))
      (q.map (fun γ => (γ 0,γ 1)))) :
    ∃ τ : Measure C(Time,X), IsFiniteMeasure τ ∧
      (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
        (τ.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t, τ.map (fun γ => γ (lowerTime t))=κ univ • q.map (fun γ => γ t)) ∧
      (∀ t, τ.map (fun γ => γ (upperTime t))=κ.map (fun γ => γ (upperTime t))) := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hc : κ univ≠∞ := measure_ne_top κ univ
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgπn,hpπn,hfinπn⟩ := normalized_optimal_subplan π hg hp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (s : Time) : πn.map (fun γ => γ s)=(κ univ)⁻¹ • κ.map (fun γ => γ s) :=
    Measure.map_smul _ (measurable_path_eval s).aemeasurable
  have hpq' : IsOptimalCoupling (πn.map (fun γ => γ 0))
      (πn.map (fun γ => γ midpointTime)) (q.map (fun γ => (γ 0,γ 1))) := by
    rwa [heval,heval]
  obtain ⟨τ,hτ,hgτ,hpτ,hl,hr⟩ := exists_optimal_left_splice πn hgπn hpπn hfinπn q hgq hpq'
  let := hτ
  refine ⟨κ univ • τ,Measure.smul_finite _ hc,?_,?_,?_,?_⟩
  · exact hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  · have hh := hpτ.smul hκ0 hc
    rw [heval,heval,smul_smul,smul_smul,ENNReal.mul_inv_cancel hκ0 hc,one_smul,one_smul] at hh
    rwa [Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable]
  · intro t
    rw [Measure.map_smul _ (measurable_path_eval _).aemeasurable,hl]
  · intro t
    rw [Measure.map_smul _ (measurable_path_eval _).aemeasurable,hr,heval,
      smul_smul,ENNReal.mul_inv_cancel hκ0 hc,one_smul]

end RegularPointCoordinates

end

end OAI
