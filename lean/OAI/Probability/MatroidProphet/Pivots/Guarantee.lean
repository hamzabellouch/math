import OAI.Probability.MatroidProphet.Pivots.Patterns

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

noncomputable def markedPivotPatterns (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun t => ∃ time : Occurrence r q → ℕ,
    OldOrdered time ∧ Function.Injective time ∧ ∃ movableMark : Fin q → Bool,
      RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t)

lemma card_markedPivotPatterns_le (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) (s : ℕ) (hqs : q ≤ s)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E) :
    (markedPivotPatterns M b a test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  let family := retainedFamily (r := r) M b a
  let affine := fun J : Finset (Occurrence r q) => affinePatterns
    (fun f : Fin n => patternLinear M (occurrenceLabel b a) J (test f))
    (fun f : Fin n => patternConstant M (occurrenceLabel b a) J (test f) s oldMark)
  have hsub : markedPivotPatterns M b a test oldMark ⊆ family.biUnion affine := by
    intro t ht
    obtain ⟨time, horder, htime, movableMark, hrecords⟩ := (Finset.mem_filter.mp ht).2
    apply Finset.mem_biUnion.mpr
    refine ⟨retained M b a time, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, time, horder, rfl⟩
    · apply mem_affinePatterns.mpr
      exact recordsPivots_affine M b a test s hqs oldMark movableMark time horder htime hground t hrecords
  have hcard (J : Finset (Occurrence r q)) :
      (affine J).card ≤ ∑ k ∈ Finset.Iic q, n.choose k := by
    simpa [affine] using card_affinePatterns_le
      (fun f : Fin n => patternLinear M (occurrenceLabel b a) J (test f))
      (fun f : Fin n => patternConstant M (occurrenceLabel b a) J (test f) s oldMark)
  have hfamily : family.card ≤ 4 ^ s :=
    (card_retainedFamily_arbitrary_old M b a
      (fun k hk => hground (Sum.inl ⟨k, hk⟩))).trans
      (Nat.pow_le_pow_right (by decide) hqs)
  have hsum : (∑ k ∈ Finset.Iic q, n.choose k) ≤ ∑ k ∈ Finset.Iic s, n.choose k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hqs) (fun _ _ _ => Nat.zero_le _)
  calc
    (markedPivotPatterns M b a test oldMark).card ≤ (family.biUnion affine).card := Finset.card_le_card hsub
    _ ≤ ∑ J ∈ family, (affine J).card := Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ family, ∑ k ∈ Finset.Iic q, n.choose k := Finset.sum_le_sum (fun J _ => hcard J)
    _ = family.card * (∑ k ∈ Finset.Iic q, n.choose k) := by simp
    _ ≤ 4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := Nat.mul_le_mul hfamily hsum

end Pivots
end MatroidProphet

end OAI
