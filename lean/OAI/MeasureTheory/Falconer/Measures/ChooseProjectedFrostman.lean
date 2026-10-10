import OAI.MeasureTheory.Falconer.Slicing.GaussianProjectionEnergy
import OAI.MeasureTheory.Falconer.Measures.NormalizedProjectedFrostman

namespace OAI

/-! # A compact original law and one projected law with the same Frostman exponent -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem choose_projected_frostman (μ : ProbabilityMeasure (Space d))
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hum : u < (m:ℝ))
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ∃ P : Space d →L[ℝ] Space m, ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u D := by
  have hsource := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) hu hus hfrost
  obtain ⟨A,hA⟩ := (gaussian_projected_energy_finite_ae (m := m)
    (μ : Measure (Space d)) hu hum hsource).exists
  let P := gaussianRowMap A
  let dims : Bool → ℕ | false => d | true => m
  let maps : ∀ b, Space d →L[ℝ] Space (dims b)
    | false => ContinuousLinearMap.id ℝ (Space d)
    | true => P
  have henergy : ∀ b, PlanarFalconer.rieszEnergyOn
      ((μ : Measure (Space d)).map (maps b)) u < ∞ := by
    intro b
    cases b with
    | false => simpa [maps,dims] using hsource
    | true => exact hA
  obtain ⟨ν,hK,hdom,D,hD,hbounds⟩ := normalized_projected_frostman μ dims maps hu henergy
  refine ⟨P,ν,hK,hdom,D,hD,?_,hbounds true⟩
  simpa [maps,dims] using hbounds false

end Falconer

end OAI
