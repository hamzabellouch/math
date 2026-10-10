import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestDetection

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

universe u

theorem exists_polynomial_cyclic_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p →
      ∀ (w : Fin 1 → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℂ),
      (∀ x, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
        (fun x => T.eval (fun _ => (x.val : ℤ)))‖ →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) f := by
  obtain ⟨c, _, hc⟩ := exists_cyclicNiltestDetection.{u} s
  let R := (Polynomial.X + P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp w hw T hT N _ f hf hcorr
  let q := p + P.eval₂ (Nat.castRingHom ℝ) p
  have hP : 0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := natPolynomial_eval_nonneg P hp
  have hq : 0 ≤ q := add_nonneg hp hP
  have hPq : P.eval₂ (Nat.castRingHom ℝ) p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcorrq := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  have hn := hc D q hq w hw T (hT.mono hPq) N f hf hcorrq
  have hbudget : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hn

end Erdos3

end

end OAI
