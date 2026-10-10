import OAI.MeasureTheory.Falconer.Slicing.GaussianProjectionEnergy
import OAI.MeasureTheory.Falconer.Measures.NormalizedProjectedFrostman

namespace OAI

/-! # Simultaneous original, first-projection and second-projection ball bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m k : ℕ}

theorem choose_second_projected_frostman (μ : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space m) {u : ℝ} (hu : 0 < u) (huk : u < (k:ℝ))
    (hsource : PlanarFalconer.rieszEnergyOn (μ : Measure (Space d)) u < ∞)
    (hfirst : PlanarFalconer.rieszEnergyOn ((μ : Measure (Space d)).map P) u < ∞) :
    ∃ Q : Space m →L[ℝ] Space k, ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      ∃ C : ℝ, 0 < C ∧ FrostmanBallBound (ν : Measure (Space d)) u C ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u C ∧
        FrostmanBallBound ((ν : Measure (Space d)).map (Q.comp P)) u C := by
  obtain ⟨A,hA⟩ := (gaussian_projected_energy_finite_ae (m := k)
    ((μ : Measure (Space d)).map P) hu huk hfirst).exists
  let Q := gaussianRowMap A
  let dims : Option Bool → ℕ | none => d | some false => m | some true => k
  let maps : ∀ i, Space d →L[ℝ] Space (dims i)
    | none => ContinuousLinearMap.id ℝ (Space d)
    | some false => P
    | some true => Q.comp P
  have henergy : ∀ i, PlanarFalconer.rieszEnergyOn
      ((μ : Measure (Space d)).map (maps i)) u < ∞ := by
    intro i
    cases i with
    | none => simpa [maps,dims] using hsource
    | some i =>
      cases i with
      | false => exact hfirst
      | true =>
        rw [Measure.map_map Q.continuous.measurable P.continuous.measurable] at hA
        exact hA
  obtain ⟨ν,hK,hdom,C,hC,hbounds⟩ := normalized_projected_frostman μ dims maps hu henergy
  refine ⟨Q,ν,hK,hdom,C,hC,?_,hbounds (some false),hbounds (some true)⟩
  simpa [maps,dims] using hbounds none

end Falconer

end OAI
