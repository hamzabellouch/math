import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRetentionTransport
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRootFibers

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] theorem mem_successfulChoices (M : MergedPairs F) (C : SplitChoice F) :
    C ∈ successfulChoices M ↔
    Function.Injective C.tuple.generator ∧
    (∀ i, C.tuple.generator i ≠ C.line.1) ∧
    Function.Injective (tuplePoint M C.tuple) ∧
    ∀ i, OnLine (tuplePoint M C.tuple i) C.line := by
  simp only [successfulChoices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_successful_prescription {M : MergedPairs F} {g : Direction F}
    {C : SplitChoice F} (hC : C ∈ successfulChoices M) (hdir : C.line.1 = g) :
    ∃ a ∈ successfulPrescriptions M g, a.choice M = C := by
  rcases C with ⟨l, T⟩
  change l.1 = g at hdir
  obtain ⟨hinj, havoid, hpoints, hline⟩ := (mem_successfulChoices M _).mp hC
  let a := RootPrescription.ofTuple g T hinj (by simpa only [hdir] using havoid)
  have htuple : a.tuple = T := rfl
  have hl : (a.choice M).line = l := by
    change lineThrough g (tuplePoint M T 0) = l
    rw [← hdir]
    exact Prod.ext rfl (hline 0)
  have hchoice : a.choice M = (⟨l, T⟩ : SplitChoice F) := by
    change (⟨(a.choice M).line, T⟩ : SplitChoice F) = ⟨l, T⟩
    rw [hl]
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l.2, ?_⟩, ?_⟩, hchoice⟩
  · intro i
    simpa only [htuple, ← hdir] using hline i
  · simpa only [htuple] using hpoints

theorem prescription_choice_mem_successful {M : MergedPairs F} {g : Direction F}
    {a : RootPrescription g} (ha : a ∈ successfulPrescriptions M g) :
    a.choice M ∈ successfulChoices M := by
  apply (mem_successfulChoices M _).mpr
  exact ⟨RootPrescription.injective a, fun i => (a.1 i).2,
    (Finset.mem_filter.mp ha).2.2, choice_on_line_of_successful ha⟩

theorem successfulTest_at_target_eq_image (M : MergedPairs F) (g : Direction F)
    (P : SplitChoice F → Prop) :
    successfulTest M (fun C => C.line.1 = g ∧ P C) =
      ((successfulPrescriptions M g).filter (fun a => P (a.choice M))).image
        (fun a => a.choice M) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC, hdir, hP⟩ := (mem_successfulTest M _ C).mp hC
    obtain ⟨a, ha, heq⟩ := exists_successful_prescription hC hdir
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, by simpa only [heq] using hP⟩, heq⟩
  · intro hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨ha, hP⟩ := Finset.mem_filter.mp ha
    exact (mem_successfulTest M _ _).mpr
      ⟨prescription_choice_mem_successful ha, rfl, hP⟩

theorem successfulTest_at_target_card (M : MergedPairs F) (g : Direction F)
    (P : SplitChoice F → Prop) :
    (successfulTest M (fun C => C.line.1 = g ∧ P C)).card =
      ((successfulPrescriptions M g).filter (fun a => P (a.choice M))).card := by
  rw [successfulTest_at_target_eq_image]
  exact Finset.card_image_of_injective _ (RootPrescription.choice_injective M)

theorem successfulTest_card_eq_sum_prescriptions (M : MergedPairs F)
    (P : SplitChoice F → Prop) :
    (successfulTest M P).card = ∑ g : Direction F,
      ((successfulPrescriptions M g).filter (fun a => P (a.choice M))).card := by
  have hfiber (g : Direction F) :
      (successfulTest M P).filter (fun C => C.line.1 = g) =
        successfulTest M (fun C => C.line.1 = g ∧ P C) := by
    ext C
    simp only [Finset.mem_filter, mem_successfulTest]
    tauto
  rw [Finset.card_eq_sum_card_fiberwise (f := fun C : SplitChoice F => C.line.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp only [hfiber, successfulTest_at_target_card]

end
end Balanced.CandidateRetentionTransport

end OAI
