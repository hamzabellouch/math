import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePointFamily

namespace OAI

namespace Balanced.CandidatePointConsumerAudit
noncomputable section
open scoped Classical
open MeasureTheory CandidateIncidenceTests CandidateRetentionTransport
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

theorem ineligible_count_eq_zero (M : MergedPairs F) (y : Point F)
    (K : Line F) (h : OnLine y K) :
    count M (Sum.inr (Sum.inl (y,K))) = 0 := by
  simp [count, h]

theorem zeroth_moment (t : Test F) :
    (∫ M, (count M t : ℝ)^0 ∂(offsetLaw F).toMeasure) = 1 := by
  simp

theorem ineligible_positive_moment (y : Point F) (K : Line F)
    (h : OnLine y K) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inl (y,K))) : ℝ)^(s+1)
      ∂(offsetLaw F).toMeasure) = 0 := by
  simp [ineligible_count_eq_zero _ _ _ h]

theorem literal_point_count (M : MergedPairs F) (y : Point F) :
    (CandidateIncidence.allModel (CandidatePointIncidence.pointTest y)).count M =
      ((successfulTest M (fun A => y ∈ designated M A)).card : ℝ) := by
  exact CandidateIncidenceTests.point_model_count y M

theorem uniform_point_moments (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ y : Point F,
      (∫ M, (count M (Sum.inl y) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤ C ∧
      ∀ K : Line F,
      (∫ M, (count M (Sum.inr (Sum.inl (y,K))) : ℝ)^s
        ∂(offsetLaw F).toMeasure) ≤ C :=
  exists_point_families_raw_moment_bound s

end
end Balanced.CandidatePointConsumerAudit

end OAI
