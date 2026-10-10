import OAI.Geometry.RCD.Transport.PointedTransportMarginals

namespace OAI

/-! # Identification of the marginals of a limiting endpoint law -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
attribute [local instance] pathBorel pathBorelSpace

theorem mapped_plan_limit_marginals
    (P : ℕ → ProbabilityMeasure C(Time,X)) (v : ℕ → X → Y)
    (hm : ∀ k, Measurable (v k)) (ν₀ ν₁ : ℕ → ProbabilityMeasure X)
    (hend0 : ∀ k, (P k : Measure C(Time,X)).map (fun γ => γ 0)=ν₀ k)
    (hend1 : ∀ k, (P k : Measure C(Time,X)).map (fun γ => γ 1)=ν₁ k)
    {Q : ProbabilityMeasure (Y×Y)}
    (hpair : Tendsto (fun k => (P k).map (fun γ => (v k (γ 0),v k (γ 1)))) atTop (𝓝 Q))
    {α β : ProbabilityMeasure Y}
    (hα : Tendsto (fun k => (ν₀ k).map (v k)) atTop (𝓝 α))
    (hβ : Tendsto (fun k => (ν₁ k).map (v k)) atTop (𝓝 β)) :
    (Q : Measure (Y×Y)).map Prod.fst=α ∧ (Q : Measure (Y×Y)).map Prod.snd=β := by
  have heq (k : ℕ) (j : Time) (ν : ProbabilityMeasure X)
      (hj : (P k : Measure C(Time,X)).map (fun γ => γ j)=ν) :
      (P k).map (fun γ => v k (γ j))=ν.map (v k) := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    calc
      _ = Measure.map ((v k) ∘ fun γ => γ j) (P k : Measure C(Time,X)) := rfl
      _ = Measure.map (v k) ((P k : Measure C(Time,X)).map (fun γ => γ j)) :=
        (Measure.map_map (hm k) (measurable_path_eval j)).symm
      _ = _ := congrArg (Measure.map (v k)) hj
  have hp0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hpair continuous_fst
  have hp1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hpair continuous_snd
  have he (k : ℕ) : Measurable (fun γ : C(Time,X) => (v k (γ 0),v k (γ 1))) :=
    ((hm k).comp (measurable_path_eval 0)).prodMk ((hm k).comp (measurable_path_eval 1))
  have hf (k : ℕ) :
      ((P k).map (fun γ => (v k (γ 0),v k (γ 1)))).map Prod.fst=(ν₀ k).map (v k) := by
    calc
      _ = (P k).map (fun γ => v k (γ 0)) := by
        apply ProbabilityMeasure.toMeasure_injective
        simpa only [ProbabilityMeasure.toMeasure_map,Function.comp_def] using
          Measure.map_map measurable_fst (he k) (μ := (P k : Measure C(Time,X)))
      _ = _ := heq k 0 (ν₀ k) (hend0 k)
  have hg (k : ℕ) :
      ((P k).map (fun γ => (v k (γ 0),v k (γ 1)))).map Prod.snd=(ν₁ k).map (v k) := by
    calc
      _ = (P k).map (fun γ => v k (γ 1)) := by
        apply ProbabilityMeasure.toMeasure_injective
        simpa only [ProbabilityMeasure.toMeasure_map,Function.comp_def] using
          Measure.map_map measurable_snd (he k) (μ := (P k : Measure C(Time,X)))
      _ = _ := heq k 1 (ν₁ k) (hend1 k)
  simp only [hf] at hp0
  simp only [hg] at hp1
  have hh0 := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hp0 hα)
  have hh1 := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hp1 hβ)
  simpa only [ProbabilityMeasure.toMeasure_map] using And.intro hh0 hh1

end RegularPointCoordinates

end

end OAI
