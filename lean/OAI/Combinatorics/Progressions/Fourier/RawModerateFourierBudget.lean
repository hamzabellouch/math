import OAI.Combinatorics.Progressions.Dynamics.RelativeModerateUniformBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem rawModerateBlock_fourier_controls {b n q M K : ℕ} [NeZero b] [NeZero K] {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin n → RetainedCubeSlice q M B T η)
    (hη : 0 < η) (hB : 0 < B) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (d : Fin b → FiniteCoefficientSlice) (t : Fin b → Fin n → FiniteCubeSlice q)
    (hd : ∀ a, (c a).finiteSlice (offset a) (stride a) = d a) (ht : ∀ a j, (s a j).finiteSlice = t a j)
    (v : Fin b → ℤ → ℝ) (w : Fin b → Fin n → (Option (Fin q) → ℤ) → ℝ)
    (hv : ∀ a z, 0 ≤ v a z) (hw : ∀ a j z, 0 ≤ w a j z)
    (hc : ∀ a x, (c a).sliceWeight x = v a (((c a).finiteSlice (offset a) (stride a)).value x))
    (hs : ∀ a j x, (s a j).sliceWeight x = w a j ((s a j).finiteSlice.coordinates x))
    (vtotal : ∀ a, 0 < ∑ x : (d a).Domain, v a ((d a).value x))
    (htotal : ∀ a j, 0 < ∑ x : (t a j).Domain, w a j ((t a j).coordinates x))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (V : ℕ) (hV : 1 ≤ V)
    (hstride : ∀ a, 0 < stride a) (hstrideV : ∀ a, stride a ≤ V)
    {O F D E : ℝ} (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (|(offset a : ℝ)| + (stride a : ℝ) * (c a).length) *
      (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ((c a).length * ∏ j, ((s a j).length : ℝ)))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (hcpower : ∀ a, (K : ℝ) ≤ E * ((c a).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    (retainedFourierBudget n n q b J.card p M V A B T η O F D E).Controls
      (rawModerateBlockSource d t v w hv hw vtotal htotal) (rawModerateBlockSum d t J)
      K (affineTorusFactor q n b (O + 1) F * K) := by
  apply IntegerFourierBudget.controls_of_complexMean _
    (retainedModerateBlockSource c s hη) (rawModerateBlockSource d t v w hv hw vtotal htotal)
    (retainedModerateBlockSum c s offset stride J) (rawModerateBlockSum d t J)
    K (affineTorusFactor q n b (O + 1) F * K)
    (fun center f => retainedModerateBlockSum_raw_complexMean c s hη offset stride d t hd ht
      v w hv hw hc hs vtotal htotal J center f)
  exact retainedModerateFourier_controls c s hη hB offset stride A hA V hV hstride hstrideV
    hO hD hE hroot hupper hlower p hpower hcpower J hJ hblocks

end Erdos3

end

end OAI
