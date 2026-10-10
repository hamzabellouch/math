import OAI.Combinatorics.Progressions.Estimates.NativeMixedDerivativeResiduals
import OAI.Combinatorics.Progressions.Estimates.QuarticNativeMixed

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_quartic_exchanged_fourier_correlation_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
        ∃ i : Fin M.outputDim, ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
          ∃ χ : (ZMod N × ZMod N) → AddChar (ZMod N) ℂ, ∀ t ∈ Q,
            Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 n *
                star (multiplicativeDerivative
                  (fun x => M.evalCyclic N i (correlationInput t.2 x)) t.1 n)) (χ t)‖ := by
  obtain ⟨A, _, hmixed⟩ := exists_quartic_native_mixed_correlation
  obtain ⟨B, _, hdifference⟩ :=
    NativeMixedCorrelation.exists_differenced_residual_correlations 3 (by omega)
  obtain ⟨D, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + Polynomial.C B) ^ B
  let T := (V + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + V + T)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  let t := (v + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htotal : u + v + t ≤ (p + C) ^ C := by
    simpa [X, U, V, T, u, v, t, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  obtain ⟨W⟩ := hmixed hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  obtain ⟨i, Q, hQ, hQdense, hQcorr⟩ :=
    hdifference hu ((Real.exp_le_exp.mpr hvC).trans hN) hf W
  let signal (a : ZMod N × ZMod N) (n : ZMod N) :=
    multiplicativeDerivative (multiplicativeDerivative f a.1) a.2 n *
      star (multiplicativeDerivative
        (fun x => W.mixed.evalCyclic N i (correlationInput a.2 x)) a.1 n)
  have hsignal (a : ZMod N × ZMod N) (n : ZMod N) : ‖signal a n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one _ (multiplicativeDerivative_norm_le_one f hf a.1) a.2 n)).trans
      (multiplicativeDerivative_norm_le_one _ (fun x => W.mixed.norm_eval i _) a.1 n)
  have hchar (a : ZMod N × ZMod N) (ha : a ∈ Q) : ∃ χ : AddChar (ZMod N) ℂ,
      Real.exp (-t) ≤ ‖finiteFourierCoeff (signal a) χ‖ := by
    obtain ⟨R⟩ := (hQcorr a ha).2
    let E := NativeIntegerExpansion.ofTest R.test R.complexity (fun _ => rfl)
    exact hfourier hv E (signal a) (hsignal a) R.correlation
  let χ (a : ZMod N × ZMod N) : AddChar (ZMod N) ℂ :=
    if ha : a ∈ Q then Classical.choose (hchar a ha) else 1
  refine ⟨W.mixed.mono huC, W.hasMixedCorrelation.mono huC, i, Q, hQ, ?_, χ, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hvC))
      (sq_nonneg _)).trans hQdense
  · intro a ha
    change Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff (signal a) (χ a)‖
    dsimp only [χ]
    rw [dite_eq_left ha]
    exact (Real.exp_le_exp.mpr (neg_le_neg htC)).trans (Classical.choose_spec (hchar a ha))

theorem exists_quartic_exchanged_fourier_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        ∃ i : Fin M.outputDim, ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
          ∃ χ : (ZMod N × ZMod N) → AddChar (ZMod N) ℂ, ∀ t ∈ Q,
            Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 n *
                star (multiplicativeDerivative
                  (fun x => M.evalCyclic N i (correlationInput t.2 x)) t.1 n)) (χ t)‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_exchanged_fourier_correlation_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

end OAI
