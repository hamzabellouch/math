import OAI.Combinatorics.Progressions.Geometry.QuarticAntisymmetricBox
import OAI.Combinatorics.Progressions.Geometry.QuarticBoxFactorizationTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_factored_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ R : NativeQuarticBoxFactorization (W.tensorPower 6) N ((p + C) ^ C),
          Real.exp (-((p + C) ^ C)) ≤
            (boxPhaseMoment 4 (fun x : Fin 4 → ZMod N =>
              (W.tensorPower 6).quarticAntisymmetric R.leftIndex R.rightIndex (fun a => (x a).val))).re := by
  obtain ⟨a, _, hbox⟩ := exists_quartic_antisymmetric_box
  obtain ⟨b, _, hstep⟩ := exists_quartic_box_step_drop_indices
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let B := 7 * (Q + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (B + (B + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  let r := 7 * (q + 1)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hr : 0 ≤ r := hq.trans hqr
  have hsum : r + (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, B, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hstepC : (r + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨M, W, hdim, hsymm, hdiag, E, i, j, hbias⟩ :=
    hbox hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let V := W.tensorPower 6
  have hrV : tensorPowerBudget 6 ((p + a) ^ a) = r := by
    norm_num [tensorPowerBudget, r, q]
  have hVr : 0 ≤ tensorPowerBudget 6 ((p + a) ^ a) := by rw [hrV]; exact hr
  have hqV : q ≤ tensorPowerBudget 6 ((p + a) ^ a) := by rw [hrV]; exact hqr
  have hVN : Real.exp ((tensorPowerBudget 6 ((p + a) ^ a) + b) ^ b) ≤ (N : ℝ) := by
    rw [hrV]
    exact (Real.exp_le_exp.mpr hstepC).trans hN
  obtain ⟨R, hi, hj⟩ := hstep hVr V i j hVN
    ((Real.exp_le_exp.mpr (neg_le_neg hqV)).trans hbias)
  have hRcost : (tensorPowerBudget 6 ((p + a) ^ a) + b) ^ b ≤ (p + C) ^ C := by
    rw [hrV]
    exact hstepC
  let R' := R.mono (tensorPowerBudget_mono 6 hqC) hRcost
  refine ⟨M.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC, R', ?_⟩
  change Real.exp (-((p + C) ^ C)) ≤
    (boxPhaseMoment 4 (fun x : Fin 4 → ZMod N =>
      V.quarticAntisymmetric R.leftIndex R.rightIndex (fun a => (x a).val))).re
  rw [hi, hj]
  exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hbias

end Erdos3

end

end OAI
