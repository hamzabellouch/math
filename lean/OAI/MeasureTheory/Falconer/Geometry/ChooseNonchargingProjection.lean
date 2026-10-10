import OAI.MeasureTheory.Falconer.Radial.ProjectedHyperplaneNull
import OAI.MeasureTheory.Falconer.Measures.ChooseProjectedFrostman

namespace OAI

/-! # Select a noncharging projection and one common compact Frostman law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem choose_noncharging_projected_frostman (μ : ProbabilityMeasure (Space d))
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hum : u < (n+1:ℕ))
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      (μ : Measure (Space d)) {x | x-p ∈ V} = 0) :
    ∃ P : Space d →L[ℝ] Space (n+1), ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ t : ℝ,
        ((ν : Measure (Space d)).map P) {y | inner ℝ w y = t} = 0) ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u D := by
  have hsource := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) hu hus hfrost
  obtain ⟨A,hA,hn⟩ := ((gaussian_projected_energy_finite_ae (m := n+1)
    (μ : Measure (Space d)) hu hum hsource).and
      (gaussian_projected_hyperplanes_null_ae (μ : Measure (Space d)) hnull)).exists
  let P := gaussianRowMap A
  let dims : Bool → ℕ | false => d | true => n+1
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
  refine ⟨P,ν,hK,hdom,?_,D,hD,?_,hbounds true⟩
  · intro w hw t
    exact (hdom.map P.continuous.measurable) (hn w hw t)
  · simpa [maps,dims] using hbounds false

end Falconer

end OAI
