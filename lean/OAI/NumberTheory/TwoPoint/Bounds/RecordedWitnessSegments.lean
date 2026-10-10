import OAI.NumberTheory.TwoPoint.Walks.WitnessSegmentation

namespace OAI

/-! Every actual main/witness family is represented in the finite segment catalog. -/

namespace TwoPointCorrelations

open scoped Classical

def recordedWitnessWord {n : ℕ} (main : List SignedStep) (word : Fin n → List SignedStep) :
    List SignedStep := main ++ (List.ofFn word).flatten

theorem recorded_witness_segments {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) :
    ∃ d : WitnessSegmentation n (recordedWitnessWord main word).length,
      (recordedWitnessWord main word).take d.1.val = main ∧
      ∀ i, ((recordedWitnessWord main word).drop (d.2.1 i).val).take (d.2.2 i).val = word i := by
  let v := recordedWitnessWord main word
  have hmain : main.length ≤ v.length := by simp [v, recordedWitnessWord]
  have hseg (i : Fin n) : ∃ start len : Fin (v.length + 1),
      (v.drop start.val).take len.val = word i := by
    obtain ⟨before, after, he⟩ := List.mem_iff_append.mp
      (List.mem_ofFn.mpr ⟨i, rfl⟩ : word i ∈ List.ofFn word)
    let preword := main ++ before.flatten
    have hv : v = preword ++ (word i ++ after.flatten) := by
      simp only [v, recordedWitnessWord, he, List.flatten_append, List.flatten_cons,
        preword, List.append_assoc]
    have hs : preword.length ≤ v.length := by rw [hv]; simp
    have hl : (word i).length ≤ v.length := by rw [hv]; simp; omega
    refine ⟨⟨preword.length, by omega⟩, ⟨(word i).length, by omega⟩, ?_⟩
    change (v.drop preword.length).take (word i).length = word i
    rw [hv, List.drop_left, List.take_left]
  choose start len hsegments using hseg
  refine ⟨(⟨main.length, Nat.lt_succ_of_le hmain⟩, start, len), ?_, hsegments⟩
  exact List.take_left

end TwoPointCorrelations

end OAI
