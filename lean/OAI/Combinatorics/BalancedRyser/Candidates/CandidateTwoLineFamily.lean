import OAI.Combinatorics.BalancedRyser.Candidates.CandidateTwoLineMoments
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceCountTransport
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceTests

namespace OAI

namespace Balanced.CandidateTwoLineFamily

noncomputable section
open scoped Classical BigOperators
open CandidateIncidenceSums CandidateIncidence CandidateRetentionTransport TupleAlignment
open MeasureTheory

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance twoLineFamilyMeasurableSpace : MeasurableSpace F := ⊤

omit [Field F] in
theorem nonconstituent_iff (M : MergedPairs F) (L : Line F) :
    L ∉ constituentLines M ↔ ∀ b, M L.1 b ≠ L.2 := by
  constructor
  · intro h b hb
    apply h
    exact Finset.mem_image.mpr ⟨(L.1,b),Finset.mem_univ _,Prod.ext rfl hb⟩
  · intro h hm
    obtain ⟨⟨d,b⟩,_,heq⟩ := Finset.mem_image.mp hm
    have hd : d = L.1 := congrArg Prod.fst heq
    have hb : M d b = L.2 := congrArg Prod.snd heq
    rw [hd] at hb
    exact h b hb

omit [Field F] in
theorem allowed_iff (L K : Line F) (M : MergedPairs F) :
    M ∈ twoLineAllowed L K ↔
      L ≠ K ∧ L ∉ constituentLines M ∧ K ∉ constituentLines M := by
  simp only [twoLineAllowed, Set.mem_ofPred_eq, nonconstituent_iff]

omit [Fintype F] in
theorem positions_iff_points (M : MergedPairs F) (L K : Line F) (C : SplitChoice F)
    (hinj : Function.Injective (tuplePoint M C.tuple)) :
    hitsTwoLines L K C.line.1 (tuplePoint M C.tuple) ↔
      ∃ p ∈ designated M C, ∃ r ∈ designated M C,
        p ≠ r ∧ OnLine p L ∧ OnLine r K := by
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    refine ⟨tuplePoint M C.tuple i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      tuplePoint M C.tuple j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
      fun he => hij (hinj he),hi,hj⟩
  · rintro ⟨p,hp,r,hr,hpr,hpL,hrK⟩
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨i,j,fun he => hpr (congrArg (tuplePoint M C.tuple) he),hpL,hrK⟩

theorem model_count_eq_test (L K : Line F) (M : MergedPairs F) :
    (twoLineModel L K).count M =
      (CandidateIncidenceTests.count M (Sum.inr (Sum.inr (Sum.inl (L,K)))) : ℝ) := by
  rw [twoLineModel_count, allModel_count_eq_successfulTest]
  simp only [allowed_iff, CandidateIncidenceTests.count, Nat.cast_ite, Nat.cast_zero]
  split_ifs with h
  · apply congrArg (fun s : Finset (SplitChoice F) => (s.card : ℝ))
    ext C
    simp only [mem_successfulTest]
    apply and_congr_right
    intro hC
    exact positions_iff_points M L K C ((mem_successfulChoices M C).mp hC).2.2.1
  · rfl

end
end Balanced.CandidateTwoLineFamily

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open MeasureTheory
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance twoLineRawMeasurableSpace : MeasurableSpace F := ⊤

theorem twoLine_raw_moment_le (L K : Line F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inr (Sum.inl (L,K)))) : ℝ)^s
      ∂(offsetLaw F).toMeasure) ≤
      (40960 * ((((s-1)*6 : ℕ) : ℝ)+3)^4)^s := by
  have h := CandidateIncidenceSums.twoLineModel_moment_le L K s
  simpa only [CandidateTwoLineFamily.model_count_eq_test] using h

end
end Balanced.CandidateIncidenceTests

end OAI
