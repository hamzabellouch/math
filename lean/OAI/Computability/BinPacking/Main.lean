import OAI.Computability.BinPacking.Results.Aggregate

namespace OAI

namespace BinPackingGap

theorem main_results :
    (∀ c : ℕ, ∃ I : Instance, ∃ B : ℕ,
      I.n = 5 * B ∧
      (∀ i, (1 / 6 : ℚ) < I.size i ∧ I.size i < 1) ∧
      B + c < opt I ∧ individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ)) ∧
    (∀ c : Nat, PackingGapNPHard c) ∧
    ((∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) ↔ PEqualsNP) ∧
    (PEqualsNP → ∃ algorithm : AbsoluteAdditiveAlgorithm 0,
    (∀ (items : RawInstance) (valid : items.Valid), ∃ packing : RawPacking,
      algorithm.run (BinaryEncoding.rawInstanceBits items) = some packing ∧
      packing.Feasible items ∧ packing.bins = opt (items.toInstance valid)) ∧
    algorithm.run (BinaryEncoding.rawInstanceBits []) = some ⟨0, []⟩ ∧
    (∀ input : List Bool, BinaryEncoding.decodeRawInstance input = none →
      algorithm.run input = none) ∧
    (∀ items : RawInstance, ¬ items.Valid →
      algorithm.run (BinaryEncoding.rawInstanceBits items) = none)) := by
  refine ⟨structural_additive_gap, packingGapNPHard,
    exists_absoluteAdditiveAlgorithm_iff_pEqualsNP, ?_⟩
  intro h
  exact ⟨absoluteAdditiveAlgorithm_of_pEqualsNP h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_optimal h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_empty h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_malformed h,
    absoluteAdditiveAlgorithm_of_pEqualsNP_invalid h⟩

end BinPackingGap

end OAI
