import OAI.Combinatorics.BalancedRyser.Candidates.CandidateLineHitFamily
import OAI.Combinatorics.BalancedRyser.Incidence.CandidatePointIncidenceMean

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open MeasureTheory TupleAlignment CandidateRetentionTransport CandidateIncidence
open CandidatePointIncidence
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance pointFamilyMeasurableSpace : MeasurableSpace F := ⊤

theorem point_model_count (y : Point F) (M : MergedPairs F) :
    (allModel (pointTest y)).count M = (count M (Sum.inl y) : ℝ) := by
  rw [allModel_count_eq_successfulTest]
  simp only [count]
  congr 2
  ext C
  simp [choiceTest, pointTest, designated]

theorem pointLine_model_count (y : Point F) (K : Line F) (M : MergedPairs F) :
    (allModel (pointLineTest y K)).count M =
      ((successfulTest M (fun C => OnLine y C.line ∧
        ∃ p ∈ designated M C, OnLine p K)).card : ℝ) := by
  rw [allModel_count_eq_successfulTest]
  congr 2
  ext C
  simp only [mem_successfulTest]
  constructor
  · rintro ⟨hC, htest⟩
    change (∀ i, OnLine (tuplePoint M C.tuple i) (lineThrough C.line.1 y)) ∧
      (∃ i, OnLine (tuplePoint M C.tuple i) K) at htest
    have hline := ((mem_successfulChoices M C).mp hC).2.2.2
    refine ⟨hC, ?_, ?_⟩
    · change lineEval C.line.1 y = C.line.2
      exact (htest.1 0).symm.trans (hline 0)
    · obtain ⟨i, hi⟩ := htest.2
      exact ⟨tuplePoint M C.tuple i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  · rintro ⟨hC, hy, hhit⟩
    have hline := ((mem_successfulChoices M C).mp hC).2.2.2
    refine ⟨hC, ?_, ?_⟩
    · intro i
      change lineEval C.line.1 (tuplePoint M C.tuple i) = lineEval C.line.1 y
      exact (hline i).trans hy.symm
    · obtain ⟨p, hp, hon⟩ := hhit
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i, hon⟩

theorem point_raw_moment_le (y : Point F) (s : ℕ) :
    (∫ M, (count M (Sum.inl y) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      (60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  have h := point_model_moment_le y ∅ (fun _ _ => 0) 0 s (by simp)
  have hempty (M : MergedPairs F) :
      (allModel (pointTest y)).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp only [PatternModel.fixCoordinates, Finset.notMem_empty, ite_false]
  simp only [PatternModel.fixedExpectation, Nat.zero_add] at h
  simp_rw [hempty] at h
  rw [allModel_measure] at h
  simpa only [point_model_count] using h

theorem pointLine_raw_moment_le (y : Point F) (K : Line F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inl (y,K))) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      (60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  by_cases hyK : OnLine y K
  · simp only [count, ite_eq_right (not_not.mpr hyK), Nat.cast_zero]
    cases s with
    | zero => simp
    | succ s =>
        simp only [zero_pow (Nat.succ_ne_zero s), integral_zero]
        positivity
  · have h := pointLine_model_moment_le y K hyK ∅ (fun _ _ => 0) 0 s (by simp)
    have hempty (M : MergedPairs F) :
        (allModel (pointLineTest y K)).fixCoordinates ∅ (fun _ _ => 0) M = M := by
      funext d
      simp only [PatternModel.fixCoordinates, Finset.notMem_empty, ite_false]
    simp only [PatternModel.fixedExpectation, Nat.zero_add] at h
    simp_rw [hempty] at h
    rw [allModel_measure] at h
    simpa only [pointLine_model_count, count, ite_eq_left hyK] using h

theorem exists_point_families_raw_moment_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ y : Point F,
      (∫ M, (count M (Sum.inl y) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤ C ∧
      ∀ K : Line F,
      (∫ M, (count M (Sum.inr (Sum.inl (y,K))) : ℝ)^s ∂(offsetLaw F).toMeasure) ≤ C := by
  refine ⟨(60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s, by positivity, ?_⟩
  intro F _ _ _ y
  exact ⟨point_raw_moment_le y s, fun K => pointLine_raw_moment_le y K s⟩

end
end Balanced.CandidateIncidenceTests

end OAI
