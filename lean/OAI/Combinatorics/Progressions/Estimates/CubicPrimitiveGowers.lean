import OAI.Combinatorics.Progressions.Fourier.CubicPrimitiveFourierRows
import OAI.Combinatorics.Progressions.Polynomial.DegreeTwoCrossGowers

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_cubic_primitive_gowers_three :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
        ∃ i : Fin W.outputDim,
          Real.exp (-((p + C) ^ C)) ≤ gowersNorm 3 (W.cubicPrimitiveFactor f i) := by
  obtain ⟨A, _, hrows⟩ := exists_cubic_primitive_fourier_rows
  obtain ⟨B, _, hcross⟩ := RationalFilteredNilmanifold.exists_gowers_three_of_degree_two_cross_rows
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, W, a, χ, ⟨V⟩⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hc := hcross V.model V.test hu V.complexity
    ((Real.exp_le_exp.mpr hvC).trans hN)
    (W.cubicPrimitiveFactor f a.1) (W.cubicPrimitiveFactor f a.2) χ
    (W.cubicPrimitiveFactor_norm f hf a.1) (W.cubicPrimitiveFactor_norm f hf a.2)
    (by simpa only [characterCrossRow] using V.correlation)
  exact ⟨q, hq, hqu.trans huC, W, a.2,
    (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hc⟩

end Erdos3

end

end OAI
