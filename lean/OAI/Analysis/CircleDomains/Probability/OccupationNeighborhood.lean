import OAI.Analysis.CircleDomains.Sobolev.ShrinkingOccupationEnergy
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! The square occupation density has arbitrarily small mass in quotient
neighborhoods of a dust point, because its entire fibre lies off the domain. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem exists_open_small_occupation_energy (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (P : ProbabilityMeasure (BasePathCode d)) (σ : Measure Y) (g : Y → ℝ≥0∞)
    (hg : Measurable g) (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ y, g y ^ 2 ∂σ) < ∞) (p : X) (hp : p ∈ d.dust)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set X, IsOpen O ∧ p ∈ O ∧ (∫⁻ y in π ⁻¹' O, g y ^ 2 ∂σ) < ε := by
  let ν : Measure Y := σ.withDensity (fun y => g y ^ 2)
  let : IsFiniteMeasure ν := ⟨by
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using henergy⟩
  have hnull : ν d.physicalDomainᶜ = 0 :=
    square_density_null_of_density_null σ g hg hG.measurableSet.compl
      (hocc ▸ meanCodeOccupation_compl d hU hG P)
  have hfiber : π ⁻¹' {p} ⊆ d.physicalDomainᶜ := by
    intro y hy hyG
    have hyp : π y = p := hy
    have hyU := (d.domainEquiv ⟨y, hyG⟩).property
    rw [he ⟨y, hyG⟩, hyp] at hyU
    exact disjoint_left.mp hdisj hyU hp
  have hz : ν.map π {p} = 0 := by
    rw [Measure.map_apply hπ.measurable (measurableSet_singleton p)]
    exact measure_mono_null hfiber hnull
  obtain ⟨O, hpO, hO, hm⟩ := ({p} : Set X).exists_isOpen_lt_of_lt (μ := ν.map π)
    ε (hz ▸ hε)
  refine ⟨O, hO, hpO (mem_singleton p), ?_⟩
  rwa [Measure.map_apply hπ.measurable hO.measurableSet,
    withDensity_apply _ (hπ.measurable hO.measurableSet)] at hm

end CircleDomainRigidity

end

end OAI
