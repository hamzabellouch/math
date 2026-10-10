import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConstituentTarget
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRootFibers
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical
open TupleAlignment CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def constituentFailures (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter
    (fun a => (a.choice M).line ∈ constituentLines M)

def oppositeFailures (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter
    (fun a => OppositeWitness M a.tuple (a.choice M).line)

def externalFailures (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter
    (fun a => ExternalDoubleWitness M a.tuple (a.choice M).line)

theorem successfulOn_of_mem {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    SuccessfulOn M a.tuple (a.choice M).line := by
  exact ⟨a.injective, fun i => (a.1 i).2,
    (Finset.mem_filter.mp ha).2.2, choice_on_line_of_successful ha⟩

theorem invalidPrescriptions_eq_union (M : MergedPairs F) (g : Direction F) :
    (successfulPrescriptions M g).filter (fun a => ¬ ValidChoice M g (a.choice M)) =
      constituentFailures M g ∪ oppositeFailures M g ∪ externalFailures M g := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, constituentFailures,
    oppositeFailures, externalFailures]
  by_cases ha : a ∈ successfulPrescriptions M g
  · have hw := not_valid_iff_bounded_witness (successfulOn_of_mem ha)
    change (¬ ValidChoice M g (a.choice M)) ↔ _ at hw
    simp only [ha, true_and]
    rw [hw]
    exact or_assoc.symm
  · simp only [ha, false_and, false_or]

theorem invalidSuccessCount_le_failure_sum (M : MergedPairs F) (g : Direction F) :
    invalidSuccessCount M g ≤
      (constituentFailures M g).card + (oppositeFailures M g).card +
        (externalFailures M g).card := by
  unfold invalidSuccessCount
  rw [invalidPrescriptions_eq_union]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

def prescriptionCode {g : Direction F} (a : RootPrescription g) :
    CandidatePrescribed.Code F := (a.tuple.generator, a.tuple.side)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prescriptionCode_injective {g : Direction F} :
    Function.Injective (prescriptionCode (F := F) (g := g)) := by
  intro a b hab
  apply RootPrescription.tuple_injective
  exact congrArg (fun c : CandidatePrescribed.Code F =>
    (⟨c.1, c.2⟩ : FourTuple F)) hab

theorem prescriptionCode_mem_constituentTargetCodes {M : MergedPairs F}
    {g : Direction F} {a : RootPrescription g}
    (ha : a ∈ constituentFailures M g) :
    prescriptionCode a ∈ CandidatePrescribed.constituentTargetCodes M g := by
  obtain ⟨hs, hc⟩ := Finset.mem_filter.mp ha
  obtain ⟨s, hline⟩ := (constituent_target_iff M (a.choice M).line).mp hc
  change (a.choice M).line = constituent M g s at hline
  have hmem : prescriptionCode a ∈
      CandidatePrescribed.successfulCodes M (constituent M g s) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      (Finset.mem_filter.mp hs).2.2⟩
    · exact ⟨a.injective, fun i => (a.1 i).2⟩
    · intro i
      change OnLine (tuplePoint M a.tuple i) (constituent M g s)
      rw [← hline]
      exact choice_on_line_of_successful hs i
  cases s
  · exact Finset.mem_union_left _ hmem
  · exact Finset.mem_union_right _ hmem

theorem constituentFailures_card_le (M : MergedPairs F) (g : Direction F) :
    (constituentFailures M g).card ≤
      (CandidatePrescribed.constituentTargetCodes M g).card := by
  apply Finset.card_le_card_of_injOn prescriptionCode
    (fun _ ha => prescriptionCode_mem_constituentTargetCodes ha)
  intro a _ b _ hab
  exact prescriptionCode_injective hab

theorem invalidSuccessCount_le (M : MergedPairs F) (g : Direction F) :
    invalidSuccessCount M g ≤
      (CandidatePrescribed.constituentTargetCodes M g).card +
        (oppositeFailures M g).card + (externalFailures M g).card := by
  exact (invalidSuccessCount_le_failure_sum M g).trans
    (Nat.add_le_add_right
      (Nat.add_le_add_right (constituentFailures_card_le M g) _) _)

omit [Field F] [Fintype F] in

theorem card_le_witnesses {g : Direction F} {A : Type*} [DecidableEq A]
    (bad : Finset (RootPrescription g)) (witnesses : Finset A)
    (tuple : A → FourTuple F)
    (hcover : ∀ a ∈ bad, ∃ w ∈ witnesses, tuple w = a.tuple) :
    bad.card ≤ witnesses.card := by
  calc
    bad.card = (bad.image RootPrescription.tuple).card :=
      (Finset.card_image_of_injective _ RootPrescription.tuple_injective).symm
    _ ≤ (witnesses.image tuple).card := by
      apply Finset.card_le_card
      intro T hT
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨w, hw, heq⟩ := hcover a ha
      exact Finset.mem_image.mpr ⟨w, hw, heq⟩
    _ ≤ witnesses.card := Finset.card_image_le

theorem invalidSuccessCount_le_witness_counts (M : MergedPairs F) (g : Direction F)
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (O : Finset A) (E : Finset B) (oppositeTuple : A → FourTuple F)
    (externalTuple : B → FourTuple F)
    (hO : ∀ a ∈ oppositeFailures M g, ∃ w ∈ O, oppositeTuple w = a.tuple)
    (hE : ∀ a ∈ externalFailures M g, ∃ w ∈ E, externalTuple w = a.tuple) :
    invalidSuccessCount M g ≤
      (CandidatePrescribed.constituentTargetCodes M g).card + O.card + E.card := by
  exact (invalidSuccessCount_le M g).trans
    (Nat.add_le_add
      (Nat.add_le_add_left (card_le_witnesses _ O oppositeTuple hO) _)
      (card_le_witnesses _ E externalTuple hE))

theorem candidateSlot_lower_bound_of_failures (M : MergedPairs F) (s : Slot F)
    {C : ℝ} (hC : 0 < C)
    (hH : 8 * Fintype.card F ≤ rootSuccessCount s.1 M)
    (hconst : (CandidatePrescribed.constituentTargetCodes M s.1).card ≤ Fintype.card F)
    (hopp : (oppositeFailures M s.1).card ≤ Fintype.card F)
    (hext : (externalFailures M s.1).card ≤ Fintype.card F)
    (hY : (rootFiberSquareCount M s.1 : ℝ) ≤ C * Fintype.card F) :
    (25 / C) * Fintype.card F ≤ ((candidateSlot M s).card : ℝ) := by
  have hloss : invalidSuccessCount M s.1 ≤ 3 * Fintype.card F := by
    have h := invalidSuccessCount_le M s.1
    omega
  have hmass : (5 : ℝ) * Fintype.card F + invalidSuccessCount M s.1 ≤
      rootSuccessCount s.1 M := by
    have hlossR : (invalidSuccessCount M s.1 : ℝ) ≤ 3 * Fintype.card F := by
      exact_mod_cast hloss
    have hHR : (8 : ℝ) * Fintype.card F ≤ rootSuccessCount s.1 M := by
      exact_mod_cast hH
    linarith
  simpa only [show (5 : ℝ) ^ 2 = 25 by norm_num] using
    candidateSlot_lower_bound_of_root_counts M s (by norm_num : (0 : ℝ) ≤ 5)
      hC hmass hY

end
end Balanced.CandidateValidityAssembly

end OAI
