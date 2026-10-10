import OAI.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem majorPhasePlateauBoxSignal_slice_expect
    {m : ℕ} {X : Type} {I : Type*} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I]
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (ambientN : X → ℕ) (localN : I → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial I ℤ)
    (hphysical : ∀ u ∈ integerBox localN, integerSampledSpatial β u ∈ integerBox ambientN)
    {q : ℕ} (A : ResidueBoxSlice localN q) (weight : (I → ℤ) → ℂ) :
    (𝔼 u ∈ A.integerPoints,
      majorPhasePlateauBoxSignal J k ambientN poly c P (integerSampledSpatial β u) * weight u) =
    (𝔼 u ∈ A.integerPoints,
      majorPhasePlateauSignal J k poly c P (integerSampledSpatial β u) * weight u) := by
  apply Finset.expect_congr rfl
  intro u hu
  rw [majorPhasePlateauBoxSignal_inside J k ambientN poly c P
    (integerSampledSpatial β u) (hphysical u (A.integerPoints_subset_integerBox hu))]

theorem exists_actualPathBufferedLocalMajorPacket_of_local
    {m n : ℕ} {X : Type} {I : Type*} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight n)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight n)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight n)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight n)]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (ambientN : X → ℕ) (localN : I → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J (n + 1)))) ℝ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial I ℤ)
    (hphysical : ∀ u ∈ integerBox localN, integerSampledSpatial β u ∈ integerBox ambientN)
    (score : (I → ℤ) → ℝ) (cost : ℝ) (strideBound : ℕ)
    (hlocal : ∃ q : ℕ, 0 < q ∧ q ≤ strideBound ∧
      ∃ A : ResidueBoxSlice localN q,
        IsDenseCommonStrideBox localN cost A.integerPoints ∧
        (𝔼 x : (∀ i, Fin (localN i)), score (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ A.integerPoints, score x) ∧
        ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : I => 1),
          T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
          (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
            majorPhasePlateauSignal J (n + 1) poly c P (integerSampledSpatial β x) *
              star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖) :
    ∃ packet : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold n) localN
        cost (OrdinaryPolynomialPhase.budget n),
      packet.stride ≤ strideBound ∧
      (𝔼 x : (∀ i, Fin (localN i)), score (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ packet.slice.integerPoints, score x) ∧
      (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ packet.slice.integerPoints,
        majorPhasePlateauBoxSignal J (n + 1) ambientN poly c P (integerSampledSpatial β x) *
          packet.weight x‖ := by
  obtain ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, hcorr⟩ := hlocal
  let packet : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold n) localN
      cost (OrdinaryPolynomialPhase.budget n) :=
    { stride := q
      stride_pos := hq
      slice := A
      dense := hAdense
      test := T
      norm := by rw [hTnorm]; norm_num
      complexity := hTcomplexity }
  refine ⟨packet, hqbound, hscore, ?_⟩
  change (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
    majorPhasePlateauBoxSignal J (n + 1) ambientN poly c P (integerSampledSpatial β x) *
      star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖
  rw [majorPhasePlateauBoxSignal_slice_expect J (n + 1) ambientN localN poly c P β hphysical A]
  exact hcorr

end Erdos3.VectorPolynomial

end

end OAI
