import OAI.Combinatorics.Progressions.Geometry.CubicBoxFactorizationTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_factored_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ R : NativeCubicBoxFactorization V N ((p + C) ^ C),
              Real.exp (-((p + C) ^ C)) ≤
                (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
                  V.cubicAntisymmetricPair R.leftIndex R.rightIndex h.val y.val
                    (cyclicBranchOffset k R.branch))).re := by
  obtain ⟨a, _, hbox⟩ := exists_cubic_antisymmetric_box
  obtain ⟨b, _, hstep⟩ := exists_cubic_box_step_drop_indices
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hsum : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hpow]
  have hstepC : (q + b) ^ b ≤ (p + C) ^ C := by linarith only [hsum, hq]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', hbias⟩ := hbox hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  obtain ⟨R, hi, hj, hbranch⟩ := hstep hq V branch i' j'
    ((Real.exp_le_exp.mpr hstepC).trans hN) hbias
  let R' := R.mono hqC hstepC
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, R', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · change Real.exp (-((p + C) ^ C)) ≤
      (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
        (V.mono hqC).cubicAntisymmetricPair R.leftIndex R.rightIndex h.val y.val
          (cyclicBranchOffset k R.branch))).re
    rw [hi, hj, hbranch]
    have heval : (fun k h y : ZMod N => (V.mono hqC).cubicAntisymmetricPair i' j'
        h.val y.val (cyclicBranchOffset k branch)) =
        (fun k h y : ZMod N => V.cubicAntisymmetricPair i' j'
          h.val y.val (cyclicBranchOffset k branch)) := by
      funext k h y
      simp only [NativeMultidegreeNilcharacter.cubicAntisymmetricPair,
        NativeMultidegreeNilcharacter.mono_eval]
    rw [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hbias

end Erdos3

end

end OAI
