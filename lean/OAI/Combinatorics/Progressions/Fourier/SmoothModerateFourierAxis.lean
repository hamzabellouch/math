import OAI.Combinatorics.Progressions.Estimates.SmoothModerateBlockBounds
import OAI.Combinatorics.Progressions.Fourier.FourierLawTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def moderateNormalizationThreshold (q M : ℕ) (B T : ℝ≥0) : ℕ :=
  max (scalarCubeNormalizationThreshold Empty M B T) (scalarCubeNormalizationThreshold (Fin q) M B T)

theorem moderateNormalizationThreshold_mul (q : ℕ) {M : ℕ} (hM : 0 < M) (B T : ℝ≥0) :
    moderateNormalizationThreshold q M B T ≤ M * moderateNormalizationThreshold q 1 B T := by
  unfold moderateNormalizationThreshold
  exact max_le
    ((scalarCubeNormalizationThreshold_mul Empty hM B T).trans (Nat.mul_le_mul_left M (le_max_left _ _)))
    ((scalarCubeNormalizationThreshold_mul (Fin q) hM B T).trans (Nat.mul_le_mul_left M (le_max_right _ _)))

theorem moderateNormalizationThreshold_power_budget (q : ℕ) {M : ℕ} (hM : 0 < M)
    (B T : ℝ≥0) (p : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    ⌈E * (moderateNormalizationThreshold q M B T : ℝ) ^ p⌉₊ ≤
      ⌈(E * (moderateNormalizationThreshold q 1 B T : ℝ) ^ p) * (M : ℝ) ^ p⌉₊ := by
  apply Nat.ceil_mono
  have hp : (moderateNormalizationThreshold q M B T : ℝ) ^ p ≤
      ((M * moderateNormalizationThreshold q 1 B T : ℕ) : ℝ) ^ p := by
    exact_mod_cast Nat.pow_le_pow_left (moderateNormalizationThreshold_mul q hM B T) p
  apply (mul_le_mul_of_nonneg_left hp hE).trans_eq
  push_cast
  ring

noncomputable def smoothModerateFourierAxis {b n q M K : ℕ} [NeZero b] [NeZero K] {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin n → SmoothCubeSlice q M B T)
    (hcmass : ∀ a, 0 < ∑ x, (c a).sliceWeight x) (hmass : ∀ a j, 0 < ∑ x, (s a j).sliceWeight x)
    (hB : 0 < B) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
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
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let U := affinePrimitiveEnvelope (Fin q) A (2 * B) (2 * T) M V
  let Q := affineTorusRadius (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  let R := affineTorusFactor (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  let H := moderateNormalizationThreshold q M B T
  let Kmax := ⌈E * (H : ℝ) ^ p⌉₊
  let Ccount := uniformSpectrumSizeConstant n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)
  let Ccap := uniformSpectrumAbsoluteCap n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)
  let exponent := max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card))
  let ζ := fun ε => uniformBlockRetainedBias n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
  let denom := fun ε => uniformCharacterDenominatorBound n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) (ζ ε)
  let residual := fun ε => 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) /
    (ζ ε) ^ majorArcCoverExponent n J.card
  refine largeScaleFourierAxis (smoothModerateBlockSource c s hcmass hmass)
    (smoothModerateBlockSum c s offset stride J) K Q Kmax Ccount Ccap exponent denom residual
    (fun center x _ Z => by
      simpa only [Q, Fintype.card_fin] using
        smoothModerateBlockSum_support c s offset stride hO hroot hupper J hJ center x Z) ?_
  intro hK ε hε hε1
  have hlong (L : ℕ) (hp : (K : ℝ) ≤ E * (L : ℝ) ^ p) : H ≤ L := by
    by_contra! hL
    exact (Nat.not_le_of_lt hK) (short_side_scale_bound hE hL.le hp)
  have hclong (a : Fin b) : scalarCubeNormalizationThreshold Empty M B T ≤ (c a).length :=
    (le_max_left _ _).trans (hlong (c a).length (hcpower a))
  have hslong (a : Fin b) (j : Fin n) : scalarCubeNormalizationThreshold (Fin q) M B T ≤ (s a j).length :=
    (le_max_right _ _).trans (hlong (s a j).length (hpower a j))
  have he := moderateSlice_geometric_approximation
    (fun a => (c a).normalized hB (hclong a)) (fun a j => (s a j).normalized hB (hslong a j))
    offset stride (fun a j => (s a j).root) A (2 * B) (2 * T) hA M V hV
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ht htV
    hO hD hE hε hε1 hroot hupper hlower p hpower hcpower J hJ hblocks
  dsimp only at he
  rw [smoothModerateBlockSource_normalized c s hcmass hmass hB hclong hslong,
    smoothModerateBlockSum_normalized c s hB hclong hslong] at he
  obtain ⟨S, hS, hcap, hchar, happ⟩ := he
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro center
    apply le_trans ?_ (hcap center)
    apply le_of_eq
    apply Finset.sum_congr
    · apply congrArg (fun f : Fintype (J → Fin ((2 * Q + 1) * K)) => @Finset.univ _ f)
      exact Subsingleton.elim _ _
    · intro k _
      rfl
  · intro k hk
    obtain ⟨d, hd, hdb, a, ξ, hξ, heq⟩ := hchar k hk
    refine ⟨d, hd, hdb, a, ξ, hξ, ?_⟩
    intro j
    simpa only [Nat.cast_mul, affineTorusFactor, Q] using heq j
  · intro center z hz
    change ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass (smoothModerateBlockSource c s hcmass hmass)
      (smoothModerateBlockSum c s offset stride J center) z : ℝ) : ℂ) -
      integerGridApproximation (smoothModerateBlockSource c s hcmass hmass)
        (smoothModerateBlockSum c s offset stride J center) K (R * K) S z‖ ≤ ε
    have hh := happ center z hz
    simp only [R, integerGridApproximation, Fintype.card_coe, finiteImageMass] at hh ⊢
    convert hh using 1
    apply congrArg norm
    apply congrArg₂ (fun x y : ℂ => x - y)
    · apply congrArg Complex.ofReal
      apply congrArg (fun t : ℝ => (K : ℝ) ^ J.card * t)
      unfold FiniteProbabilityWeights.mean
      apply Finset.sum_congr
      · apply Finset.ext
        intro x
        exact ⟨fun _ => Finset.mem_univ x, fun _ => Finset.mem_univ x⟩
      · intro x _
        rfl
    · apply congrArg (fun t : ℂ => ((K : ℂ) / (R * K : ℕ)) ^ J.card * t)
      apply Finset.sum_congr rfl
      intro k _
      rfl

end Erdos3

end

end OAI
