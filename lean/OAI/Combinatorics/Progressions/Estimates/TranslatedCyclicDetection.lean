import OAI.Combinatorics.Progressions.Polynomial.PolynomialCyclicDetection

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem finiteCorrelation_translate_right {H : Type*} [AddCommGroup H] [Fintype H]
    (f u : H → ℂ) (a : H) :
    finiteCorrelation Finset.univ f (fun x => u (a + x)) =
      finiteCorrelation Finset.univ (fun x => f (-a + x)) u := by
  simpa only [finiteCorrelation, add_neg_cancel_left] using
    (expect_translate (fun x => f x * star (u (a + x))) (-a)).symm

theorem exists_polynomial_translated_cyclic_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p →
      ∀ (w : Fin 1 → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (N : ℕ) [NeZero N] (a : ZMod N) (f : ZMod N → ℂ),
      (∀ x, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
        (fun x => T.eval (fun _ => ((a + x).val : ℤ)))‖ →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) f := by
  obtain ⟨C, hC, hdet⟩ := exists_polynomial_cyclic_detection.{u} s P
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp w hw T hT N _ a f hf hc
  have hc' : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ (fun x => f (-a + x))
      (fun x => T.eval (fun _ => (x.val : ℤ)))‖ := by
    rwa [finiteCorrelation_translate_right f (fun x => T.eval (fun _ => (x.val : ℤ))) a] at hc
  have hh := hdet D p hp w hw T hT N (fun x => f (-a + x)) (fun x => hf _) hc'
  simpa only [gowersNorm_translate] using hh

end Erdos3

end

end OAI
