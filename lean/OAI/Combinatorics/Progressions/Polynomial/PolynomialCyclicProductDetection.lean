import OAI.Combinatorics.Progressions.Estimates.CyclicProductDetection

namespace OAI

section

universe u v

open scoped TensorProduct

namespace Erdos3

theorem exists_polynomial_cyclic_product_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι : Type v} [Fintype ι] {L : ι → Type u}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
      ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p)) →
      ∀ (N : ℕ) [NeZero N] (h : ι → ZMod N) (f : ZMod N → ℂ),
      (∀ x, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
        (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)))‖ →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) f := by
  obtain ⟨c, _, hc⟩ := exists_cyclicProductNiltestDetection s
  let R := (Polynomial.X + P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hcorr
  let q := p + P.eval₂ (Nat.castRingHom ℝ) p
  have hP : 0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := natPolynomial_eval_nonneg P hp
  have hq : 0 ≤ q := add_nonneg hp hP
  have hPq : P.eval₂ (Nat.castRingHom ℝ) p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcorrq := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  have hn := hc D q hq (hι.trans hPq) w hw T (fun i => (hT i).mono hPq) N h f hf hcorrq
  have hbudget : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hn

end Erdos3

end

end OAI
