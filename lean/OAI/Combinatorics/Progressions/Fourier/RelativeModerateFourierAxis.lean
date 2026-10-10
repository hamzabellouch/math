import OAI.Combinatorics.Progressions.Probability.RelativeRetainedLawTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def retainedCubeFourierAxis {b n q M K : ℕ} [NeZero b] [NeZero K] {B T η : ℝ≥0}
    (s : Fin b → Fin (n + 1) → RetainedCubeSlice q M B T η) (hη : 0 < η) (hB : 0 < B)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {O F D E : ℝ}
    (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((s a j).length : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let U := affinePrimitiveEnvelope (Fin q) A (B / η) (T / η) M 1
  let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  let H := (q + 1) * M
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
  refine largeScaleFourierAxis (retainedCubeBlockSource s hη) (retainedCubeBlockSum s J)
    K Q Kmax Ccount Ccap exponent denom residual
    (fun center x _ Z => by
      simpa only [Q, Fintype.card_fin] using retainedCubeBlockSum_support s hO hroot hupper J hJ center x Z) ?_
  intro hK ε hε hε1
  have hlong (a : Fin b) (j : Fin (n + 1)) : H ≤ (s a j).length := by
    by_contra! hL
    exact (Nat.not_le_of_lt hK) (short_side_scale_bound hE hL.le (hpower a j))
  have he := weightedSlice_geometric_approximation
    (fun a j => (s a j).normalized hB hη (hlong a j)) (fun a j => (s a j).root)
    A (B / η) (T / η) hA M (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    hO hD hE hε hε1 hroot hupper hlower p hpower J hJ hblocks
  dsimp only at he
  rw [retainedCubeBlockSource_normalized s hη hB hlong,
    retainedCubeBlockSum_normalized s hB hη hlong] at he
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
    change ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass (retainedCubeBlockSource s hη)
      (retainedCubeBlockSum s J center) z : ℝ) : ℂ) -
      integerGridApproximation (retainedCubeBlockSource s hη)
        (retainedCubeBlockSum s J center) K (R * K) S z‖ ≤ ε
    have hh := happ center z hz
    simp only [R, integerGridApproximation, Fintype.card_coe, finiteImageMass] at hh ⊢
    convert hh using 1
    apply congrArg norm
    apply congrArg₂ (fun x y : ℂ => x - y)
    · apply congrArg Complex.ofReal
      apply congrArg (fun t : ℝ => (K : ℝ) ^ J.card * t)
      unfold FiniteProbabilityWeights.mean
      apply Finset.sum_congr
      · apply congrArg (fun f : Fintype (RetainedCubeBlockDomain s) => @Finset.univ _ f)
        exact Subsingleton.elim _ _
      · intro x _
        rfl
    · apply congrArg (fun t : ℂ => ((K : ℂ) / (R * K : ℕ)) ^ J.card * t)
      apply Finset.sum_congr rfl
      intro k _
      rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def retainedModerateFourierAxis {b n q M K : ℕ} [NeZero b] [NeZero K] {B T η : ℝ≥0}
    (c : Fin b → RetainedCoefficientSlice M B T η) (s : Fin b → Fin n → RetainedCubeSlice q M B T η)
    (hη : 0 < η)
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
  let U := affinePrimitiveEnvelope (Fin q) A (B / η) (T / η) M V
  let Q := affineTorusRadius (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  let R := affineTorusFactor (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  let H := (q + 1) * M
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
  refine largeScaleFourierAxis (retainedModerateBlockSource c s hη)
    (retainedModerateBlockSum c s offset stride J) K Q Kmax Ccount Ccap exponent denom residual
    (fun center x _ Z => by
      simpa only [Q, Fintype.card_fin] using
        retainedModerateBlockSum_support c s offset stride hO hroot hupper J hJ center x Z) ?_
  intro hK ε hε hε1
  have hlong (L : ℕ) (hp : (K : ℝ) ≤ E * (L : ℝ) ^ p) : H ≤ L := by
    by_contra! hL
    exact (Nat.not_le_of_lt hK) (short_side_scale_bound hE hL.le hp)
  have hclong (a : Fin b) : M ≤ (c a).length :=
    (Nat.le_mul_of_pos_left M (by omega : 0 < q + 1)).trans (hlong (c a).length (hcpower a))
  have hslong (a : Fin b) (j : Fin n) : (q + 1) * M ≤ (s a j).length :=
    hlong (s a j).length (hpower a j)
  have he := moderateSlice_geometric_approximation
    (fun a => (c a).normalized hB hη (hclong a)) (fun a j => (s a j).normalized hB hη (hslong a j))
    offset stride (fun a j => (s a j).root) A (B / η) (T / η) hA M V hV
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ht htV
    hO hD hE hε hε1 hroot hupper hlower p hpower hcpower J hJ hblocks
  dsimp only at he
  rw [retainedModerateBlockSource_normalized c s hη hB hclong hslong,
    retainedModerateBlockSum_normalized c s hB hη hclong hslong] at he
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
    change ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass (retainedModerateBlockSource c s hη)
      (retainedModerateBlockSum c s offset stride J center) z : ℝ) : ℂ) -
      integerGridApproximation (retainedModerateBlockSource c s hη)
        (retainedModerateBlockSum c s offset stride J center) K (R * K) S z‖ ≤ ε
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

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def retainedFourierBudget (n g q b j p M V : ℕ)
    (A B T η : ℝ≥0) (O F D E : ℝ) : IntegerFourierBudget :=
  let U := affinePrimitiveEnvelope (Fin q) A (B / η) (T / η) M V
  let Q := affineTorusRadius q g b (O + 1) F
  let R := affineTorusFactor q g b (O + 1) F
  let Kmax := ⌈E * (((q + 1) * M : ℕ) : ℝ) ^ p⌉₊
  let Cshort := ((R * Kmax : ℕ) : ℝ) ^ j
  let ζ := fun ε => uniformBlockRetainedBias n j (p * j)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ j) ε
  { radius := Q
    countConstant := max (uniformSpectrumSizeConstant n j (p * j)
      U ((R : ℝ) * D) (((R : ℝ) * E) ^ j)) Cshort
    countExponent := max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * (p * j))
    coefficientCap := max (uniformSpectrumAbsoluteCap n j (p * j)
      U ((R : ℝ) * D) (((R : ℝ) * E) ^ j)) Cshort
    denominatorBound := fun ε => max (uniformCharacterDenominatorBound n j (p * j)
      U ((R : ℝ) * D) (((R : ℝ) * E) ^ j) (ζ ε)) (R * Kmax : ℕ)
    residualBound := fun ε => max (2 * majorArcCoverConstant n j U ((R : ℝ) * D) /
      (ζ ε) ^ majorArcCoverExponent n j) 0 }

theorem retainedFourierBudget_coefficientCap_nonneg (n g q b j p M V : ℕ)
    (A B T η : ℝ≥0) (O F D E : ℝ) :
    0 ≤ (retainedFourierBudget n g q b j p M V A B T η O F D E).coefficientCap := by
  unfold retainedFourierBudget
  exact (pow_nonneg (Nat.cast_nonneg _) j).trans (le_max_right _ _)

theorem retainedFourierBudget_countConstant_nonneg (n g q b j p M V : ℕ)
    (A B T η : ℝ≥0) (O F D E : ℝ) :
    0 ≤ (retainedFourierBudget n g q b j p M V A B T η O F D E).countConstant := by
  unfold retainedFourierBudget
  exact (pow_nonneg (Nat.cast_nonneg _) j).trans (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def relativeCubeFourierAxis {b n q K : ℕ} [NeZero b] [NeZero K]
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
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let s := fun a j => (P a j).retainedCubeSource q R hδ hR (r a j) (w a j) B T η (hw a j) (hLip a j) (hr a j)
  have hg a := relativeProgression_family_bounds (P a) hδ hD hE (hupper a) (hlower a) p (hpower a)
  exact retainedCubeFourierAxis s hη hB A hA
    (O := δ⁻¹) (F := (2 : ℝ) ^ (n + 1) * F) (D := D * (δ⁻¹) ^ (n + 1)) (E := E * (δ⁻¹) ^ p)
    (inv_nonneg.mpr hδ.le) (by positivity) (by positivity)
    (fun a j => (hg a).2.1 j) (fun a => (hg a).2.2.1) (fun a => (hg a).2.2.2.1)
    p (fun a j => (hg a).2.2.2.2 j) J hJ hblocks

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def relativeModerateFourierAxis {b n q K : ℕ} [NeZero b] [NeZero K]
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
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let c := fun a => (C a).retainedCoefficientSource R hδ hR (rc a) (wc a) B T η (hwc a) (hLipC a) (hrc a)
  let s := fun a j => (P a j).retainedCubeSource q R hδ hR (r a j) (w a j) B T η (hw a j) (hLip a j) (hr a j)
  have hg a := relativeModerate_family_bounds (C a) (P a) hδ hD hE (hupper a) (hlower a) p (hpower a) (hcpower a)
  have hV : 1 ≤ ⌈2 / δ⌉₊ := (C ⟨0, NeZero.pos b⟩).canonicalStep_pos.trans_le
    ((C ⟨0, NeZero.pos b⟩).geometric_bounds hδ).2.2.1
  exact retainedModerateFourierAxis c s hη hB (fun a => (C a).root) (fun a => (C a).canonicalStep)
    A hA ⌈2 / δ⌉₊ hV (fun a => (C a).canonicalStep_pos) (fun a => ((C a).geometric_bounds hδ).2.2.1)
    (O := δ⁻¹) (F := (3 * (2 : ℝ) ^ n) * F) (D := D * (δ⁻¹) ^ (n + 1)) (E := E * (δ⁻¹) ^ p)
    (inv_nonneg.mpr hδ.le) (by positivity) (by positivity)
    (fun a j => ((P a j).geometric_bounds hδ).2.2.2)
    (fun a => (hg a).1) (fun a => (hg a).2.1) p
    (fun a j => (hg a).2.2.1 j) (fun a => (hg a).2.2.2) J hJ hblocks

end Erdos3

end

end OAI
