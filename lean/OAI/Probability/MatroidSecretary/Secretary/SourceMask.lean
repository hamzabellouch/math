import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Exact branch and sacrificed-mask law of the manuscript's concrete source rule.
The full-seed integral retains unused mask and parity coins.  This is the
source-law side of the secretary reconstruction, not a prefix-mask assumption. -/

namespace MatroidProphet

open MeasureTheory Finset

lemma bitsExpectation_union_three {α : Type*} [DecidableEq α]
    (p q r : α → ℝ) (V : Finset α) (f : Finset α → ℝ) :
    bitsExpectation p V (fun H => bitsExpectation q V (fun D =>
      bitsExpectation r V (fun C => f (H ∪ D ∪ C)))) =
    bitsExpectation (fun e => p e + (1 - p e) * (q e + (1 - q e) * r e)) V f := by
  simp_rw [Finset.union_assoc]
  have h (H : Finset α) := bitsExpectation_union q r V (fun U => f (H ∪ U))
  simp_rw [h]
  exact bitsExpectation_union p (fun e => q e + (1 - q e) * r e) V f

lemma source_main_mask_rate :
    (1 / 2 : ℝ) + (1 - 1 / 2) * (1 / 4 + (1 - 1 / 4) * thinningRate) =
      5 / 8 + 3 * ((2 : ℝ) ^ 143)⁻¹ := by
  norm_num [thinningRate]

lemma source_main_mask_rate_pos : 0 < (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹ := by
  norm_num

lemma source_main_mask_rate_lt_one : (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹ < 1 := by
  norm_num

lemma completeHiddenRule_mask_eq {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) :
    (completeHiddenRule M hE).mask r =
      if mainBranch r then (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
      else (mainMasks r).H := by
  rfl

lemma integral_source_branch_mask {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (f : Bool → Finset (Fin n) → ℝ) :
    (∫ r, f (mainBranch r) ((completeHiddenRule M hE).mask r) ∂sourceSeedLaw n) =
      (bitsExpectation (fun _ : Fin n => (1 / 2 : ℝ)) univ (f false) +
       bitsExpectation (fun _ : Fin n => (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹)
         univ (f true)) / 2 := by
  simp_rw [completeHiddenRule_mask_eq]
  rw [integral_sourceSeedLaw (fun d b => f b (if b then d.H ∪ d.D ∪ d.C else d.H))]
  simp only [fairParityExpectation, Bool.false_eq_true, ↓reduceIte]
  simp only [bitsExpectation_const]
  have hsplit (H D C : Finset (Fin n)) :
      ((f false H + f true (H ∪ D ∪ C)) / 2 +
        (f false H + f true (H ∪ D ∪ C)) / 2) / 2 =
      (1 / 2 : ℝ) * f false H + (1 / 2 : ℝ) * f true (H ∪ D ∪ C) := by ring
  simp_rw [hsplit, bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_const]
  rw [bitsExpectation_union_three]
  simp_rw [source_main_mask_rate]
  ring

end MatroidProphet

end OAI
