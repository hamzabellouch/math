import OAI.Combinatorics.Progressions.Estimates.QuarticAntisymmetricModel

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_antisymmetric_box_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.outputDim ^ 6),
          Real.exp (-((p + C) ^ C)) ≤
            (boxPhaseMoment 4 (fun x : Fin 4 → ZMod N =>
              (W.tensorPower 6).quarticAntisymmetric i j (fun a => (x a).val))).re := by
  obtain ⟨a, _, hanti⟩ := exists_quartic_antisymmetric_model_with_mixed
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (16 * Q + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hsum : 16 * q + 2 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hcost : 16 * q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, i, j, A, hA, hAind, hcorr⟩ :=
    hanti hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let F (x : Fin 4 → ZMod N) := (W.tensorPower 6).quarticAntisymmetric i j (fun a => (x a).val)
  let U (a : Fin 4) (x : Fin 4 → ZMod N) := A a (fun b => (x b).val)
  let e : (Fin 4 → ZMod N) ≃ ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
    { toFun := fun x => ((x 2, x 3), (x 0, x 1))
      invFun := fun t => ![t.2.1, t.2.2, t.1.1, t.1.2]
      left_inv := by intro x; funext a; fin_cases a <;> rfl
      right_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl }
  have havg : boxTestCorrelation F U =
      𝔼 t : (ZMod N × ZMod N) × (ZMod N × ZMod N),
        (W.tensorPower 6).quarticAntisymmetric i j
          ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)] *
          ∏ k, A k ![(t.2.1.val : ℤ), (t.2.2.val : ℤ), (t.1.1.val : ℤ), (t.1.2.val : ℤ)] := by
    unfold boxTestCorrelation
    apply Fintype.expect_equiv e
    intro x
    have hv : ![((x 0).val : ℤ), ((x 1).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)] =
        fun a => ((x a).val : ℤ) := by
      funext a
      fin_cases a <;> rfl
    change F x * ∏ k, U k x = (W.tensorPower 6).quarticAntisymmetric i j
      ![((x 0).val : ℤ), ((x 1).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)] *
      ∏ k, A k ![((x 0).val : ℤ), ((x 1).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]
    rw [hv]
  have hmiss : ∀ a, MissesBoxCoordinate (U a) a := by
    intro a x v
    apply hAind
    intro b hba
    change (((Function.update x a v) b).val : ℤ) = ((x b).val : ℤ)
    rw [Function.update_of_ne hba]
  have hbox : ‖boxTestCorrelation F U‖ ^ 16 ≤ (boxPhaseMoment 4 F).re :=
    boxTest_cauchySchwarz 3 F U (fun a x => hA a _) hmiss
  have hscore : Real.exp (-(16 * q)) ≤ (boxPhaseMoment 4 F).re := by
    have hc : Real.exp (-q) ≤ ‖boxTestCorrelation F U‖ := by rwa [havg]
    have hpow : Real.exp (-(16 * q)) = (Real.exp (-q)) ^ 16 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _) hc 16).trans hbox
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC, i, j, ?_⟩
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hscore

theorem exists_quartic_antisymmetric_box :
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
        ∃ i j : Fin (W.outputDim ^ 6),
          Real.exp (-((p + C) ^ C)) ≤
            (boxPhaseMoment 4 (fun x : Fin 4 → ZMod N =>
              (W.tensorPower 6).quarticAntisymmetric i j (fun a => (x a).val))).re := by
  obtain ⟨C, hC, h⟩ := exists_quartic_antisymmetric_box_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

end OAI
