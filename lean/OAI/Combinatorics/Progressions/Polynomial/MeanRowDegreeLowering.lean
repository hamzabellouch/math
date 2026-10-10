import OAI.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
import OAI.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_unit_vertical_mean_row_degree_lowering (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ H X : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : σ => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1))
          (Fin (n + 1)) ((p + C) ^ C),
        D.GeometryComplexityLE ((p + C) ^ C) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) ∧
        ∀ a b : σ → ℤ, NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (fun i x => (V.test T.orbit i).eval (x + a))
          (fun i x => (V.test T.orbit i).eval (x + b)) := by
  obtain ⟨A, _, hmodel⟩ := exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, htranslate⟩ := UnitVerticalObservable.exists_integer_translation_equivalence_budget s
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C B) ^ B + 1)
  refine ⟨C, hC, ?_⟩
  intro L σ H Y _ _ _ _ _ _ _ _ _ _ d D T p hp hT sample f hf hcorr
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + v + 1 ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨n, hn, hncard, V, hD, hVcorr⟩ := hmodel D T hp hT sample f hf hcorr
  refine ⟨n, hn, hncard.trans (Real.exp_le_exp.mpr huC), V.mono huC,
    hD.mono D huC, (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hVcorr, ?_⟩
  intro a b
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hncard
  exact (htranslate D V T.orbit hu hD hcard a b).mono hvC

end Erdos3.RationalFilteredNilmanifold

end

end OAI
