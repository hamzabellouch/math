import OAI.Combinatorics.Progressions.Dynamics.RelativeCubeUniformBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem rawCubeBlock_fourier_controls {b n q M K : ℕ} [NeZero b] [NeZero K] {B T η : ℝ≥0}
    (s : Fin b → Fin (n + 1) → RetainedCubeSlice q M B T η) (hη : 0 < η) (hB : 0 < B)
    (t : Fin b → Fin (n + 1) → FiniteCubeSlice q) (ht : ∀ a j, (s a j).finiteSlice = t a j)
    (w : Fin b → Fin (n + 1) → (Option (Fin q) → ℤ) → ℝ) (hw : ∀ a j z, 0 ≤ w a j z)
    (hs : ∀ a j x, (s a j).sliceWeight x = w a j ((s a j).finiteSlice.coordinates x))
    (htotal : ∀ a j, 0 < ∑ x : (t a j).Domain, w a j ((t a j).coordinates x))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {O F D E : ℝ}
    (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((s a j).length : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    (retainedFourierBudget n (n + 1) q b J.card p M 1 A B T η O F D E).Controls
      (rawCubeBlockSource t w hw htotal) (rawCubeBlockSum t J)
      K (affineTorusFactor q (n + 1) b (O + 1) F * K) := by
  apply IntegerFourierBudget.controls_of_complexMean _
    (retainedCubeBlockSource s hη) (rawCubeBlockSource t w hw htotal)
    (retainedCubeBlockSum s J) (rawCubeBlockSum t J) K (affineTorusFactor q (n + 1) b (O + 1) F * K)
    (fun center f => retainedCubeBlockSum_raw_complexMean s hη t ht w hw hs htotal J center f)
  exact retainedCubeFourier_controls s hη hB A hA hO hD hE hroot hupper hlower p hpower J hJ hblocks

end Erdos3

end

end OAI
