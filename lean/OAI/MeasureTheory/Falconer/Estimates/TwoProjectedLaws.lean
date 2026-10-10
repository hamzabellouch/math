import OAI.MeasureTheory.Falconer.Geometry.ChooseNonchargingProjection
import OAI.MeasureTheory.Falconer.Measures.SecondProjectedFrostman

namespace OAI

/-! # Two successive auxiliary laws with noncharging in the first target

The two exponent gaps are explicit: energy is taken below the first common
Frostman exponent before choosing the smaller auxiliary target.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem choose_two_projected_laws (μ : ProbabilityMeasure (Space d))
    {s C u v : ℝ} (hu : 0 < u) (huv : u < v) (hvs : v < s)
    (hv : v < (n+1:ℕ)) (hun : u < (n:ℝ))
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      (μ : Measure (Space d)) {x | x-p ∈ V} = 0) :
    ∃ (P : Space d →L[ℝ] Space (n+1)) (Q : Space (n+1) →L[ℝ] Space n)
      (ν : ProbabilityMeasure (Space d)),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ t : ℝ,
        ((ν : Measure (Space d)).map P) {y | inner ℝ w y = t} = 0) ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map (Q.comp P)) u D := by
  obtain ⟨P,η,_,hηdom,hηnull,D,_,hη,hηP⟩ :=
    choose_noncharging_projected_frostman μ (hu.trans huv) hvs hv hfrost hnull
  have hηenergy := rieszEnergyOn_lt_top_of_frostman (η : Measure (Space d)) hu huv hη
  have hηPenergy := rieszEnergyOn_lt_top_of_frostman ((η : Measure (Space d)).map P) hu huv hηP
  obtain ⟨Q,ν,hK,hdom,D',hD',hν,hνP,hνQ⟩ :=
    choose_second_projected_frostman η P hu hun hηenergy hηPenergy
  refine ⟨P,Q,ν,hK,hdom.trans hηdom,?_,D',hD',hν,hνP,hνQ⟩
  intro w hw t
  exact (hdom.map P.continuous.measurable) (hηnull w hw t)

end Falconer

end OAI
