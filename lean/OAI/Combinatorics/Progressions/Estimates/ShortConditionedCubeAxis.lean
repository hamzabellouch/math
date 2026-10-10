import OAI.Combinatorics.Progressions.Fourier.FourierLawTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def conditionedCubeSliceFourierAxis {b g q K : ℕ} {C : Type} [Fintype C] [NeZero K]
    (s : Fin b → Fin g → FiniteCubeSlice q) (w : CubeSliceBlockDomain s C → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (G : Finset (CubeSliceBlockDomain s C)) (hG : 0 < ∑ x ∈ G, w x)
    (coeff : C → Fin b → ℤ) (H : Fin b → ℝ)
    {O F : ℝ} (hO : 0 ≤ O) (hcoeff : ∀ c a, |(coeff c a : ℝ)| ≤ H a)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hvolume : ∀ a, H a * ∏ j, ((s a j).length : ℝ) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (Kmax : ℕ) (hKmax : K ≤ Kmax) : IntegerFourierAxis := by
  let Q := ⌈blockJetScaleBound q g b ((O + 1) ^ g * F)⌉₊
  have hmass : 0 < ∑ x, w x :=
    hG.trans_le (Finset.sum_le_univ_sum_of_nonneg (s := G) hw)
  refine boundedIntegerFourierAxis (FiniteProbabilityWeights.conditionPositiveWeights w hw hmass G hG)
    (cubeSliceBlockSum s coeff J) K Q ((2 * Q + 1) * Kmax) (Nat.mul_le_mul_left _ hKmax) ?_
  intro center x _ S
  exact (cubeSliceBlockSum_scale_bound s coeff H hO hcoeff hroot hvolume J hJ center x S).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))

noncomputable def boundedCoefficientCubeSliceAxis {b g q K : ℕ} [NeZero K]
    (s : Fin b → Fin g → FiniteCubeSlice q) (c : Fin b → FiniteCoefficientSlice)
    (w : CubeSliceBlockDomain s (∀ a, (c a).Domain) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x)
    {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hvolume : ∀ a, ((c a).radius : ℝ) * ∏ j, ((s a j).length : ℝ) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (Kmax : ℕ) (hKmax : K ≤ Kmax) : IntegerFourierAxis :=
  boundedCubeSliceFourierAxis s w hw hmass (fun x a => (c a).value (x a))
    (fun a => ((c a).radius : ℝ)) hO (fun x a => by exact_mod_cast (c a).value_abs_le (x a))
    hroot hvolume J hJ Kmax hKmax

end Erdos3

end

end OAI
