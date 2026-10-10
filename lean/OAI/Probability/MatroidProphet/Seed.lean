import OAI.Probability.MatroidProphet.Algorithm.SeedLaw
import OAI.Probability.MatroidProphet.SafeParity

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def sourceCoinProbability (j : Fin 5) : ℝ :=
  if j.val = 0 then 1/2 else if j.val = 1 then 1/4 else if j.val = 4 then 1/2 else thinningRate

lemma sourceCoinProbability_nonneg (j : Fin 5) : 0 ≤ sourceCoinProbability j := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

lemma sourceCoinProbability_le_one (j : Fin 5) : sourceCoinProbability j ≤ 1 := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

noncomputable def sourceSeedLaw (n : ℕ) : Measure (Seed (mainSeedBits n)) :=
  mainSeedLaw n sourceCoinProbability sourceCoinProbability_nonneg sourceCoinProbability_le_one

instance sourceSeedLaw_probability (n : ℕ) : IsProbabilityMeasure (sourceSeedLaw n) := by
  unfold sourceSeedLaw
  infer_instance

lemma mainMasks_encodeMainSeed {n : ℕ} (b : MainSeedBlocks n) :
    mainMasks (encodeMainSeed b) =
      ⟨seedSet b.1, seedSet b.2.1, seedSet b.2.2.1, seedSet b.2.2.2.1, b.2.2.2.2 1⟩ := by
  obtain ⟨hH, hD, hC, hT⟩ := encodeMainSeed_mask b
  have ho := encodeMainSeed_odd b
  change (encodeMainSeed b) _ = _ at ho
  simp only [mainMasks, hH, hD, hC, hT, ho]

lemma fairTwoBits (f : Bool → Bool → ℝ) :
    bitsExpectation (fun _ : Fin 2 => (1/2 : ℝ)) Finset.univ
      (fun S => f (setSeed S 0) (setSeed S 1)) =
      fairParityExpectation (fun p => fairParityExpectation (fun b => f b p)) := by
  have hu : (Finset.univ : Finset (Fin 2)) = insert 0 (insert 1 ∅) := by decide
  rw [hu, bitsExpectation_insert _ _ 0 (by decide)]
  rw [bitsExpectation_insert _ _ 1 (by decide), bitsExpectation_insert _ _ 1 (by decide)]
  simp [bitsExpectation_empty, setSeed, fairParityExpectation]
  ring

lemma integral_sourceSeedLaw {n : ℕ} (f : MainMasks n → Bool → ℝ) :
    (∫ r, f (mainMasks r) (mainBranch r) ∂sourceSeedLaw n) =
      bitsExpectation (fun _ : Fin n => (1/2 : ℝ)) Finset.univ (fun H =>
        bitsExpectation (fun _ : Fin n => (1/4 : ℝ)) Finset.univ (fun D =>
          bitsExpectation (fun _ : Fin n => thinningRate) Finset.univ (fun C =>
            bitsExpectation (fun _ : Fin n => thinningRate) Finset.univ (fun T =>
              fairParityExpectation (fun p => fairParityExpectation (fun b => f ⟨H,D,C,T,p⟩ b)))))) := by
  rw [sourceSeedLaw, mainSeedLaw_expectation]
  simp only [sourceCoinProbability]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, ite_true, ite_false,
    OfNat.ofNat_ne_zero]
  simp only [mainMasks_encodeMainSeed, encodeMainSeed_branch, seedSet_setSeed]
  apply bitsExpectation_congr
  intro H _
  apply bitsExpectation_congr
  intro D _
  apply bitsExpectation_congr
  intro C _
  apply bitsExpectation_congr
  intro T _
  exact fairTwoBits (fun b p => f ⟨H,D,C,T,p⟩ b)

end MatroidProphet

end OAI
