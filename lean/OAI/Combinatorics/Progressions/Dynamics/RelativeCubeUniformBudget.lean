import OAI.Combinatorics.Progressions.Fourier.RelativeModerateFourierAxis

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {b n q M K : ℕ} [NeZero b] [NeZero K] {B T η : ℝ≥0}
    (s : Fin b → Fin (n + 1) → RetainedCubeSlice q M B T η) (hη : 0 < η) (hB : 0 < B)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {O F D E : ℝ}
    (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((s a j).length : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b)

theorem retainedCubeFourierAxis_budget :
    (retainedCubeFourierAxis s hη hB A hA hO hD hE hroot hupper hlower p hpower J hJ hblocks).budget =
      retainedFourierBudget n (n + 1) q b J.card p M 1 A B T η O F D E := by
  simp only [IntegerFourierAxis.budget, retainedCubeFourierAxis, largeScaleFourierAxis,
    IntegerFourierAxis.ofEstimate, Fintype.card_fin, Fintype.card_coe, retainedFourierBudget,
    affineTorusFactor]

include hB hA hO hD hE hroot hupper hlower hpower hJ hblocks in
theorem retainedCubeFourier_controls :
    (retainedFourierBudget n (n + 1) q b J.card p M 1 A B T η O F D E).Controls
      (retainedCubeBlockSource s hη) (retainedCubeBlockSum s J)
      K (affineTorusFactor q (n + 1) b (O + 1) F * K) := by
  have h := (retainedCubeFourierAxis s hη hB A hA hO hD hE hroot hupper hlower p hpower J hJ hblocks).budget_controls
  rw [retainedCubeFourierAxis_budget] at h
  simpa only [retainedCubeFourierAxis, largeScaleFourierAxis, IntegerFourierAxis.ofEstimate,
    Fintype.card_fin, affineTorusFactor] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem relativeCubeFourierAxis_budget {b n q K : ℕ} [NeZero b] [NeZero K]
    {δ : ℝ} (P : Fin b → Fin (n + 1) → RelativeProgression δ) (hδ : 0 < δ)
    (R : ℕ) (hR : 0 < R) (r : ∀ a j, (P a j).CubeResidueLabel q R)
    (w : Fin b → Fin (n + 1) → (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hB : 0 < B) (hη : 0 < η)
    (hw : ∀ a j x, 0 ≤ w a j x ∧ w a j x ≤ B) (hLip : ∀ a j, LipschitzWith T (w a j))
    (hr : ∀ a j, r a j ∉ ((P a j).cubeReference q hδ).lowWeightFibers
      (((P a j).cubeSlice q).residueLabelMap (fun _ => (P a j).canonicalStep * R))
      (fun x => translatedCubeWeight (P a j).parentLength 0 (w a j) (((P a j).cubeSlice q).coordinates x)) η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {F D E : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hupper : ∀ a, (∏ j, ((P a j).parentLength : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((P a j).parentLength : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((P a j).parentLength : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    (relativeCubeFourierAxis P hδ R hR r w B T η hB hη hw hLip hr A hA
      hD hE hupper hlower p hpower J hJ hblocks).budget =
      retainedFourierBudget n (n + 1) q b J.card p (⌈2 / δ⌉₊ * R) 1 A B (T * 2) η
        δ⁻¹ ((2 : ℝ) ^ (n + 1) * F) (D * (δ⁻¹) ^ (n + 1)) (E * (δ⁻¹) ^ p) := by
  simp only [relativeCubeFourierAxis, IntegerFourierAxis.budget, retainedCubeFourierAxis,
    largeScaleFourierAxis, IntegerFourierAxis.ofEstimate, Fintype.card_fin, Fintype.card_coe,
    retainedFourierBudget, affineTorusFactor]

end Erdos3

end

end OAI
