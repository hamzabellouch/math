import OAI.Probability.MatroidProphet.Seed
import OAI.Probability.MatroidProphet.Algorithm.Worst
import OAI.Probability.MatroidProphet.Maximum.Mask

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

noncomputable def mainPayoff {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) : ℝ :=
  bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (fun H =>
    mainMean ⟨H, ∅, ∅, ∅, false⟩
      (fun d => mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))))

lemma mainPayoff_nonneg {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) : 0 ≤ mainPayoff M hE w := by
  apply bitsExpectation_nonneg _ (fun _ => by norm_num) (fun _ => by norm_num)
  intro H _
  have h := mainMean_mono (⟨H, ∅, ∅, ∅, false⟩ : MainMasks n)
    (fun d _ => mainWorstRounded_nonneg M hE d (fun e => roundedLevel weightBase (w e)))
  simpa only [mainMean_const] using h

lemma mainMean_H {n : ℕ} (d : MainMasks n) (f : Finset (Fin n) → ℝ) :
    mainMean d (fun d' => f d'.H) = f d.H := by
  simp only [mainMean, tripleMaskExpectation, withMasks,
    fairParityExpectation_const, bitsExpectation_const]

lemma integral_sourceSeedLaw_mainMean {n : ℕ} (f : MainMasks n → Bool → ℝ) :
    (∫ r, f (mainMasks r) (mainBranch r) ∂sourceSeedLaw n) =
      bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (fun H =>
        mainMean ⟨H, ∅, ∅, ∅, false⟩ (fun d => fairParityExpectation (fun b => f d b))) := by
  simpa only [mainMean, tripleMaskExpectation, withMasks] using integral_sourceSeedLaw f

lemma completeHiddenRule_lower {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed (mainSeedBits n)) :
    (if mainBranch r then
      mainWorstRounded M hE (mainMasks r) (fun e => roundedLevel weightBase (w e))
    else maximumForMask M w (mainMasks r).H) ≤
      hiddenWorstReward (completeHiddenRule M hE) w r := by
  rw [completeHiddenRule, branchHiddenRule_worst]
  cases hb : mainBranch r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [roundedMaximum_worst_mask]
  · simp only [↓reduceIte]
    exact mainWorstRounded_le_hiddenWorstReward M hE r w hw

lemma integrated_branch_lower {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    (mainPayoff M hE w + maximumPayoff M w) / 2 ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  have h := integral_mono (μ := sourceSeedLaw n) Integrable.of_finite Integrable.of_finite
    (fun r => completeHiddenRule_lower M hE w hw r)
  have heq : (∫ r, (if mainBranch r then
      mainWorstRounded M hE (mainMasks r) (fun e => roundedLevel weightBase (w e))
      else maximumForMask M w (mainMasks r).H) ∂sourceSeedLaw n) =
      (mainPayoff M hE w + maximumPayoff M w) / 2 := by
    rw [integral_sourceSeedLaw_mainMean (fun d b => if b then
      mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))
      else maximumForMask M w d.H)]
    have hf : (fun d : MainMasks n => fairParityExpectation (fun b => if b then
        mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))
        else maximumForMask M w d.H)) =
        (fun d => (1/2 : ℝ) *
          (mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e)) + maximumForMask M w d.H)) := by
      funext d
      simp only [fairParityExpectation, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [hf]
    simp_rw [mainMean_mul, mainMean_add, mainMean_H]
    rw [bitsExpectation_mul_const, bitsExpectation_add, ← maximumPayoff_eq_masks]
    change (1/2 : ℝ) * (mainPayoff M hE w + maximumPayoff M w) = _
    ring
  rw [heq] at h
  exact h

end MatroidProphet

end OAI
