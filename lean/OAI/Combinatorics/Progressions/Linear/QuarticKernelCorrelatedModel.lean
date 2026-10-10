import OAI.Combinatorics.Progressions.Geometry.QuarticAntisymmetricBox
import OAI.Combinatorics.Progressions.Geometry.QuarticBoxFactorizationTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_kernel_correlated_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ R : NativeMixedCorrelation 3 N ((p + C) ^ C) f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * R.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) R.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (R.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.outputDim ^ 6),
          Nonempty (NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
            Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ)))) := by
  obtain ⟨a, _, hbox⟩ := exists_quartic_antisymmetric_box_with_mixed
  obtain ⟨b, _, hcorrelate⟩ := exists_quartic_kernel_correlation
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let V := 7 * (Q + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (V + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  let v := 7 * (q + 1)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqv : q ≤ v := by dsimp only [v]; linarith
  have hv : 0 ≤ v := hq.trans hqv
  have hsum : v + (v + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, V, q, v, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (v + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hpow, hqv]
  have hcorrC : (v + b) ^ b ≤ (p + C) ^ C := by linarith only [hsum, hv]
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, i, j, hbias⟩ :=
    hbox hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  have hvV : tensorPowerBudget 6 ((p + a) ^ a) = v := by
    norm_num [tensorPowerBudget, v, q]
  have hVpos : 0 ≤ tensorPowerBudget 6 ((p + a) ^ a) := by rw [hvV]; exact hv
  have hqV : q ≤ tensorPowerBudget 6 ((p + a) ^ a) := by rw [hvV]; exact hqv
  obtain ⟨S⟩ := hcorrelate hVpos (W.tensorPower 6) i j
    ((Real.exp_le_exp.mpr (neg_le_neg hqV)).trans hbias)
  have hcost : (tensorPowerBudget 6 ((p + a) ^ a) + b) ^ b ≤ (p + C) ^ C := by
    rw [hvV]
    exact hcorrC
  obtain ⟨R, hR⟩ := hret
  rcases hR with rfl
  exact ⟨R.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC,
    i, j, ⟨S.mono hcost⟩⟩

end Erdos3

end

end OAI
