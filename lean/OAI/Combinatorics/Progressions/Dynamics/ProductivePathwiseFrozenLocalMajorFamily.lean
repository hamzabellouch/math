import OAI.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_productive_pathwise_frozen_localMajor_family
    {Ω X η : Type*} [Fintype Ω] (keep : Ω → I → Prop) {n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    (law : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost B δ : ℝ) (hcost : 0 ≤ cost)
    (hB : 1 ≤ B) (hshort : ∀ z i, ¬keep z i → (N i : ℝ) ≤ B)
    (physical : Ω → (I → ℤ) → X) (signal : η → X → ℂ)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep z i} → ℤ, (∀ i, 0 ≤ fixed i ∧ fixed i < N i.val) ∧
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold n)
        (fun i : {i // keep z i} => N i.val) cost (OrdinaryPolynomialPhase.budget n),
        δ ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          signal j (physical z (finiteSplitPoint (keep z) x fixed)) * A.weight x‖) :
    ∃ chosen : Ω → Option η → LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold n)
        N (max cost (Real.log B)) (OrdinaryPolynomialPhase.budget n),
      ∀ j, δ * law.mass (good j) ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox N) => (chosen z a).weight x.val) (signal j) := by
  obtain ⟨chosen, _, hchosen⟩ := exists_productive_localMajorSlice_coordinate_family
    (OrdinaryPolynomialPhase.nilmanifold n) law good N hN (max cost (Real.log B))
    (OrdinaryPolynomialPhase.budget n) δ
    (OrdinaryPolynomialPhase.zeroLocalMajorSlice N hN (max cost (Real.log B))
      (hcost.trans (le_max_left _ _))) physical signal (by
        intro j z hz
        obtain ⟨fixed, hfixed, A, hA⟩ := hlocal j z hz
        let starts := frozenShortStarts (keep z) fixed
        have hstarts := frozenShortStarts_inside (keep z) fixed hfixed
        refine ⟨A.freezeShort (keep z) starts hstarts hB (hshort z), ?_⟩
        rw [A.expect_freezeShort (keep z) starts hstarts hB (hshort z)
          (fun x => signal j (physical z x))]
        simpa only [starts,
          frozenLongExtension_shortStarts (keep z) fixed (fun i => (hfixed i).1)] using hA)
  exact ⟨chosen, hchosen⟩

end Erdos3

end

end OAI
