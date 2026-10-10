import OAI.Combinatorics.Progressions.Fourier.RelativeModerateFourierAxis

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {b n q M K : ℕ} [NeZero b] [NeZero K] {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin n → RetainedCubeSlice q M B T η)
    (hη : 0 < η) (hB : 0 < B) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (V : ℕ) (hV : 1 ≤ V)
    (ht : ∀ a, 0 < stride a) (htV : ∀ a, stride a ≤ V)
    {O F D E : ℝ} (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (|(offset a : ℝ)| + (stride a : ℝ) * (c a).length) *
      (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ((c a).length * ∏ j, ((s a j).length : ℝ)))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (hcpower : ∀ a, (K : ℝ) ≤ E * ((c a).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b)

theorem retainedModerateFourierAxis_budget :
    (retainedModerateFourierAxis c s hη hB offset stride A hA V hV ht htV
      hO hD hE hroot hupper hlower p hpower hcpower J hJ hblocks).budget =
      retainedFourierBudget n n q b J.card p M V A B T η O F D E := by
  simp only [IntegerFourierAxis.budget, retainedModerateFourierAxis, largeScaleFourierAxis,
    IntegerFourierAxis.ofEstimate, Fintype.card_fin, Fintype.card_coe, retainedFourierBudget,
    affineTorusFactor]

include hB hA hV ht htV hO hD hE hroot hupper hlower hpower hcpower hJ hblocks in
theorem retainedModerateFourier_controls :
    (retainedFourierBudget n n q b J.card p M V A B T η O F D E).Controls
      (retainedModerateBlockSource c s hη) (retainedModerateBlockSum c s offset stride J)
      K (affineTorusFactor q n b (O + 1) F * K) := by
  have h := (retainedModerateFourierAxis c s hη hB offset stride A hA V hV ht htV
    hO hD hE hroot hupper hlower p hpower hcpower J hJ hblocks).budget_controls
  rw [retainedModerateFourierAxis_budget] at h
  simpa only [retainedModerateFourierAxis, largeScaleFourierAxis, IntegerFourierAxis.ofEstimate,
    Fintype.card_fin, affineTorusFactor] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem relativeModerateFourierAxis_budget {b n q K : ℕ} [NeZero b] [NeZero K]
    {δ : ℝ} (C : Fin b → RelativeProgression δ) (P : Fin b → Fin n → RelativeProgression δ) (hδ : 0 < δ)
    (R : ℕ) (hR : 0 < R) (rc : ∀ a, (C a).CoefficientResidueLabel R)
    (r : ∀ a j, (P a j).CubeResidueLabel q R)
    (wc : Fin b → (Option Empty → ℝ) → ℝ) (w : Fin b → Fin n → (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hB : 0 < B) (hη : 0 < η)
    (hwc : ∀ a x, 0 ≤ wc a x ∧ wc a x ≤ B) (hLipC : ∀ a, LipschitzWith T (wc a))
    (hw : ∀ a j x, 0 ≤ w a j x ∧ w a j x ≤ B) (hLip : ∀ a j, LipschitzWith T (w a j))
    (hrc : ∀ a, rc a ∉ ((C a).coefficientReference hδ).lowWeightFibers ((C a).coefficientSlice.residueLabelMap R)
      (fun x => wc a (fun _ => (((C a).coefficientSlice.value x : ℤ) : ℝ) / (C a).parentLength)) η)
    (hr : ∀ a j, r a j ∉ ((P a j).cubeReference q hδ).lowWeightFibers
      (((P a j).cubeSlice q).residueLabelMap (fun _ => (P a j).canonicalStep * R))
      (fun x => translatedCubeWeight (P a j).parentLength 0 (w a j) (((P a j).cubeSlice q).coordinates x)) η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {F D E : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hupper : ∀ a, ((C a).parentLength : ℝ) * (∏ j, ((P a j).parentLength : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * (((C a).parentLength : ℝ) * ∏ j, ((P a j).parentLength : ℝ)))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((P a j).parentLength : ℝ) ^ p)
    (hcpower : ∀ a, (K : ℝ) ≤ E * ((C a).parentLength : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    (relativeModerateFourierAxis C P hδ R hR rc r wc w B T η hB hη hwc hLipC hw hLip hrc hr
      A hA hD hE hupper hlower p hpower hcpower J hJ hblocks).budget =
      retainedFourierBudget n n q b J.card p (⌈2 / δ⌉₊ * R) ⌈2 / δ⌉₊ A B (T * 2) η
        δ⁻¹ ((3 * (2 : ℝ) ^ n) * F) (D * (δ⁻¹) ^ (n + 1)) (E * (δ⁻¹) ^ p) := by
  simp only [relativeModerateFourierAxis, IntegerFourierAxis.budget, retainedModerateFourierAxis,
    largeScaleFourierAxis, IntegerFourierAxis.ofEstimate, Fintype.card_fin, Fintype.card_coe,
    retainedFourierBudget, affineTorusFactor]

end Erdos3

end

end OAI
