import OAI.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
import OAI.Combinatorics.Progressions.Estimates.QuarticCyclicDiagonalComparison
import OAI.Combinatorics.Progressions.Fourier.QuarticExchangedFourier

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_second_exchange_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
        ∃ i : Fin M.outputDim, ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, Real.exp (-((p + C) ^ C)) ≤
            ‖finiteCorrelation Finset.univ
              (multiplicativeDerivative
                (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2)
              (multiplicativeDerivative
                (multiplicativeDerivative
                  (fun x => M.evalCyclic N i (correlationInput t.1.2 x)) t.1.1) t.2)‖ := by
  obtain ⟨A, _, hfourier⟩ := exists_quartic_exchanged_fourier_correlation_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * U + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, U, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, i, H, _, hdense, χ, hcorr⟩ :=
    hfourier hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let F (a : ZMod N × ZMod N) := multiplicativeDerivative (multiplicativeDerivative f a.1) a.2
  let V (a : ZMod N × ZMod N) :=
    multiplicativeDerivative (fun x => M.evalCyclic N i (correlationInput a.2 x)) a.1
  let G (a : ZMod N × ZMod N) (n : ZMod N) := V a n * χ a n
  have hF (a : ZMod N × ZMod N) (n : ZMod N) : ‖F a n‖ ≤ 1 :=
    multiplicativeDerivative_norm_le_one _ (multiplicativeDerivative_norm_le_one f hf a.1) a.2 n
  have hV (a : ZMod N × ZMod N) (n : ZMod N) : ‖V a n‖ ≤ 1 :=
    multiplicativeDerivative_norm_le_one _ (fun x => M.norm_eval i _) a.1 n
  have hG (a : ZMod N × ZMod N) (n : ZMod N) : ‖G a n‖ ≤ 1 := by
    dsimp only [G]
    rw [norm_mul, AddChar.norm_apply, mul_one]
    exact hV a n
  have hc (a : ZMod N × ZMod N) (ha : a ∈ H) :
      Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ (F a) (G a)‖ := by
    simpa only [F, G, V, finiteFourierCoeff, finiteCorrelation, star_mul, mul_assoc,
      mul_comm, mul_left_comm]
      using hcorr a ha
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := exists_many_family_derivative_correlations F G H hF hG
    (Real.exp_pos (-q)) (Real.exp_pos (-q)) (by
      simpa only [Fintype.card_prod, ZMod.card, Nat.cast_mul, pow_two] using hdense) hc
  have hprod : Real.exp (-q) * Real.exp (-q) ^ 2 = Real.exp (-(3 * q)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) * Real.exp (-q) ^ 2 / 2 := by
    rw [hprod]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -(3 * q) - 1)).trans
      (exp_sub_one_le_half_exp (-(3 * q)))
  refine ⟨M.mono hqC, hret.mono hqC, i, Q, hQ, ?_, ?_⟩
  · have hsize : Real.exp (-q) * Real.exp (-q) ^ 2 / 2 * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) := by
      convert hQsize using 1
      simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul]
      ring
    exact (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans hsize
  · intro a ha
    have hc' := hsmall.trans (hQcorr a ha).2
    change Real.exp (-((p + C) ^ C)) ≤
      ‖finiteCorrelation Finset.univ (multiplicativeDerivative (F a.1) a.2)
        (multiplicativeDerivative (fun n => V a.1 n * χ a.1 n) a.2)‖ at hc'
    rw [norm_derivative_correlation_mul_addChar] at hc'
    dsimp only [F] at hc'
    rw [multiplicativeDerivative_comm (multiplicativeDerivative f a.1.1) a.1.2 a.2] at hc'
    exact hc'

theorem exists_quartic_second_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        ∃ i : Fin M.outputDim, ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, Real.exp (-((p + C) ^ C)) ≤
            ‖finiteCorrelation Finset.univ
              (multiplicativeDerivative
                (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2)
              (multiplicativeDerivative
                (multiplicativeDerivative
                  (fun x => M.evalCyclic N i (correlationInput t.1.2 x)) t.1.1) t.2)‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_second_exchange_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.mixedSecondDifferenceWithShift_diagonal
    {s : ℕ} {p : ℝ} (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : Fin 4 → ℤ) (i : Fin M.outputDim) (h n k l : ℤ) :
    M.mixedSecondDifferenceWithShift c ((i, i), (i, i)) ![h, n, k, l] =
      integerDoubleDifferenceWithShift (fun z => M.eval i (correlationInput h z)) k l c n := by
  have hinput (j : Fin 4) : mixedSecondDifferenceInput j ![h, n, k, l] + ![0, c j] =
      correlationInput h (n + ![0, k, l, k + l] j + c j) := by
    funext a
    fin_cases a
    · change h + 0 = h
      exact add_zero h
    · rfl
  simp only [NativeMultidegreeNilcharacter.mixedSecondDifferenceWithShift, hinput,
    integerDoubleDifferenceWithShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    add_zero, add_assoc]

theorem exists_quartic_carry_intervals_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
        ∃ i : Fin M.outputDim, ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ (b : Fin 3 → Fin 3) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b)
                    ((i, i), (i, i)) ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨A, _, hexchange⟩ := exists_quartic_second_exchange_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + 5)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + A) ^ A
  have htotal : q + 5 ≤ (p + C) ^ C := by
    simpa [X, U, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have h24 : (24 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (24 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) / 24 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
    calc
      _ ≤ Real.exp (-((p + C) ^ C)) * Real.exp 5 :=
        mul_le_mul_of_nonneg_left h24 (Real.exp_nonneg _)
      _ = Real.exp (-((p + C) ^ C) + 5) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨M, hret, i, Q, hQ, hQdense, hQcorr⟩ :=
    hexchange hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  refine ⟨M.mono hqC, hret.mono hqC, i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (by positivity)).trans hQdense
  · intro t ht
    let R (z : ℤ) := M.eval i (correlationInput (t.1.2.val : ℤ) z)
    let g := multiplicativeDerivative
      (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2
    have hg (x : ZMod N) : ‖g x‖ ≤ 1 :=
      multiplicativeDerivative_norm_le_one _
        (multiplicativeDerivative_norm_le_one _
          (multiplicativeDerivative_norm_le_one f hf t.1.1) t.2) t.1.2 x
    have hR : (fun n : ZMod N => R n.val) =
        (fun x => M.evalCyclic N i (correlationInput t.1.2 x)) := by
      funext x
      apply congrArg (M.eval i)
      funext j
      fin_cases j <;> rfl
    have hc : Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ g
        (multiplicativeDerivative (multiplicativeDerivative (fun n : ZMod N => R n.val) t.1.1) t.2)‖ := by
      rw [hR]
      exact hQcorr t ht
    obtain ⟨b, a, len, hlen, hend, hshort, hcor, hvol⟩ :=
      exists_cyclic_double_difference_interval g R t.1.1 t.2 (Real.exp_pos (-q)) hg
        (fun n => M.norm_eval i _) hc
    refine ⟨b, a, len, hlen, hend, hshort, hsmall.trans hvol, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤
      ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), g (n : ZMod N) *
        star (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b)
          ((i, i), (i, i)) ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖
    simpa only [M.mixedSecondDifferenceWithShift_diagonal] using hsmall.trans hcor

theorem exists_quartic_carry_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        ∃ i : Fin M.outputDim, ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ (b : Fin 3 → Fin 3) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b)
                    ((i, i), (i, i)) ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_carry_intervals_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_quartic_unwrapped_intervals_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ i : Fin M.outputDim, ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ (b : Fin 3 → Fin 3) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim),
            ∃ l : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count,
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  multiplicativeDerivative
                    (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                    star (M.mixedSecondDifferenceWithShift 0 v
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                    star ((((E b).selectedExpansion ((i, i), (i, i)) v).test l).eval
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_quartic_carry_intervals_with_mixed
  obtain ⟨B, _, htranslate⟩ := NativeMultidegreeNilcharacter.exists_mixed_second_difference_translation 3
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + 2 * V)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + 2 * r ≤ (p + C) ^ C := by
    simpa [X, U, V, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, i, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let E (b : Fin 3 → Fin 3) := htranslate M (doubleDifferenceCarryShift N b)
  refine ⟨M.mono hqC, hret.mono hqC, r, hr, hrC, E, i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (by positivity)).trans hQdense
  · intro t ht
    obtain ⟨b, a, len, hlen, hend, hshort, hvol, hcor⟩ := hQcorr t ht
    obtain ⟨v, l, hc⟩ := (E b).transfer_sample_correlation
      (Finset.Ico (a : ℤ) (a + len))
      (fun n => ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])
      ((i, i), (i, i))
      (fun n => multiplicativeDerivative
        (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N))
      (fun n _ => M.mixedSecondDifferenceWithShift_unit 0 _) hcor
    exact ⟨b, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      v, l, (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hc⟩

theorem exists_quartic_unwrapped_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ i : Fin M.outputDim, ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ (b : Fin 3 → Fin 3) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim),
            ∃ l : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count,
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  multiplicativeDerivative
                    (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                    star (M.mixedSecondDifferenceWithShift 0 v
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                    star ((((E b).selectedExpansion ((i, i), (i, i)) v).test l).eval
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_unwrapped_intervals_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_quartic_fixed_unwrapped_intervals_with_mixed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        M.HasMixedCorrelation f ∧
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ (i : Fin M.outputDim) (b : Fin 3 → Fin 3)
          (v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
          (l : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count),
        ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ a len : ℕ,
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (M.mixedSecondDifferenceWithShift 0 v
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star ((((E b).selectedExpansion ((i, i), (i, i)) v).test l).eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_quartic_unwrapped_intervals_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * U + 6)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 6 ≤ (p + C) ^ C := by
    simpa [X, U, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, r, hr, hrq, E, i, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let K := Σ b : Fin 3 → Fin 3,
    Σ v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim),
      Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count
  let R (t : (ZMod N × ZMod N) × ZMod N) (_ : Unit) (c : K) : Prop :=
    ∃ a len : ℕ,
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
        ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          multiplicativeDerivative
            (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
            star (M.mixedSecondDifferenceWithShift 0 c.2.1
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
            star ((((E c.1).selectedExpansion ((i, i), (i, i)) c.2.1).test c.2.2).eval
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖
  have hchoice : ∀ t ∈ Q, ∀ u, ∃ c, R t u c := by
    intro t ht _
    obtain ⟨b, a, len, hlen, hend, hshort, hvol, v, l, hcor⟩ := hQcorr t ht
    exact ⟨⟨b, v, l⟩, a, len, hlen, hend, hshort, hvol, hcor⟩
  have hinner (b : Fin 3 → Fin 3) :
      (Fintype.card (Σ v : (Fin M.outputDim × Fin M.outputDim) ×
        (Fin M.outputDim × Fin M.outputDim),
          Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count) : ℝ) ≤ Real.exp (2 * r) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ ≤ ∑ _v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim),
          Real.exp r := Finset.sum_le_sum (fun v _ => ((E b).selectedExpansion ((i, i), (i, i)) v).count_bound)
      _ = (Fintype.card ((Fin M.outputDim × Fin M.outputDim) ×
          (Fin M.outputDim × Fin M.outputDim)) : ℝ) * Real.exp r := by simp
      _ ≤ Real.exp r * Real.exp r :=
        mul_le_mul_of_nonneg_right (E b).right_dimension (Real.exp_nonneg _)
      _ = Real.exp (2 * r) := by rw [← Real.exp_add, two_mul]
  have hcount : (Fintype.card K : ℝ) ≤ Real.exp (2 * q + 5) := by
    change (Fintype.card (Σ b : Fin 3 → Fin 3,
      Σ v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim),
        Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _b : Fin 3 → Fin 3, Real.exp (2 * r) := Finset.sum_le_sum (fun b _ => hinner b)
      _ = 27 * Real.exp (2 * r) := by norm_num
      _ ≤ Real.exp 5 * Real.exp (2 * r) := mul_le_mul_of_nonneg_right
        ((by norm_num : (27 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)) (Real.exp_nonneg _)
      _ = Real.exp (5 + 2 * r) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c, S, _, hS, hSdense, hfixed⟩ := exists_large_fixed_choices Q hQ R hchoice hcount
  have hsize : Real.exp (-(2 * q + 5)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  refine ⟨M.mono hqC, hret.mono hqC, r, hr, hrq.trans hqC, E, i, (c ()).1, (c ()).2.1, (c ()).2.2, S, hS, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(3 * q + 5)) * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-(2 * q + 5)) * (Real.exp (-q) * (N : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * q + 5)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨a, len, hlen, hend, hshort, hvol, hcor⟩ := hfixed t ht ()
    exact ⟨a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hcor⟩

theorem exists_quartic_fixed_unwrapped_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) ((p + C) ^ C),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ (i : Fin M.outputDim) (b : Fin 3 → Fin 3)
          (v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
          (l : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count),
        ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ a len : ℕ,
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (M.mixedSecondDifferenceWithShift 0 v
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star ((((E b).selectedExpansion ((i, i), (i, i)) v).test l).eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_fixed_unwrapped_intervals_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_quartic_multilinear_intervals_with_mixed :
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
        ∃ r u : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧ 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ F : NativeIntegerVectorEquivalence 3 u (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval),
        ∃ (i : Fin M.outputDim) (b : Fin 3 → Fin 3)
          (v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
          (z : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count),
        ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ a len : ℕ,
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ (w : QuarticSixFactorIndex (Fin W.outputDim)) (z' : Fin (F.selectedExpansion v w).count),
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (quarticSixMain W.eval w.1
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star ((((E b).selectedExpansion ((i, i), (i, i)) v).test z).eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star (((F.selectedExpansion v w).test z').eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_quartic_fixed_unwrapped_intervals_with_mixed
  obtain ⟨B, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_quartic_six_factor_multilinearization
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := (P + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 3 * U + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + A) ^ A
  let u := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have htotal : q + 3 * u + 2 ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have htransferC : q + 2 * u ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, r, hr, hrq, E, i, b, v, z, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  obtain ⟨W, hdim, hsymm, hdiag, F⟩ := hcompare M
  refine ⟨M.mono hqC, hret.mono hqC, W.mono huC, hdim, hsymm, hdiag.mono huC,
    r, u, hr, hrq.trans hqC, hu, huC, E, F, i, b, v, z, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (by positivity)).trans hQdense
  · intro t ht
    obtain ⟨a, len, hlen, hend, hshort, hvol, hcor⟩ := hQcorr t ht
    let D (n : ℤ) := multiplicativeDerivative
      (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N)
    let T (n : ℤ) := (((E b).selectedExpansion ((i, i), (i, i)) v).test z).eval
      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]
    have hc : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        (D n * star (T n)) * star (M.mixedSecondDifferenceWithShift 0 v
          ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
      have hswap (n : ℤ) :
          D n * star (M.mixedSecondDifferenceWithShift 0 v
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) * star (T n) =
            (D n * star (T n)) * star (M.mixedSecondDifferenceWithShift 0 v
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) := mul_right_comm _ _ _
      calc
        _ ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            D n * star (M.mixedSecondDifferenceWithShift 0 v
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) * star (T n)‖ := hcor
        _ = _ := by simp only [hswap]
    obtain ⟨w, z', hw⟩ := NativeIntegerVectorEquivalence.quartic_six_factor_sample_correlation W F
      (Finset.Ico (a : ℤ) (a + len)) (t.1.2.val : ℤ) (t.1.1.val : ℤ) (t.2.val : ℤ)
      v (fun n => D n * star (T n)) hc
    refine ⟨a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol, w, z', ?_⟩
    have hfinal := (Real.exp_le_exp.mpr (neg_le_neg htransferC)).trans hw
    have horder (n : ℤ) :
        (D n * star (T n)) * star (quarticSixMain W.eval w.1
            ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
            star (((F.selectedExpansion v w).test z').eval
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) =
          D n * star (quarticSixMain W.eval w.1
            ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) * star (T n) *
            star (((F.selectedExpansion v w).test z').eval
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) :=
      congrArg (fun c : ℂ => c * star (((F.selectedExpansion v w).test z').eval
        ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])) (mul_right_comm _ _ _)
    simp only [horder] at hfinal
    exact hfinal

theorem exists_quartic_multilinear_intervals :
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
        ∃ r u : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧ 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ F : NativeIntegerVectorEquivalence 3 u (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval),
        ∃ (i : Fin M.outputDim) (b : Fin 3 → Fin 3)
          (v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
          (z : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count),
        ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ a len : ℕ,
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ (w : QuarticSixFactorIndex (Fin W.outputDim)) (z' : Fin (F.selectedExpansion v w).count),
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (quarticSixMain W.eval w.1
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star ((((E b).selectedExpansion ((i, i), (i, i)) v).test z).eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star (((F.selectedExpansion v w).test z').eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_multilinear_intervals_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_quartic_fixed_multilinear_intervals_with_mixed :
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
        ∃ r u : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧ 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ F : NativeIntegerVectorEquivalence 3 u (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval),
        ∃ (i : Fin M.outputDim) (b : Fin 3 → Fin 3)
          (v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
          (z : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count),
        ∃ (w : QuarticSixFactorIndex (Fin W.outputDim)) (z' : Fin (F.selectedExpansion v w).count),
        ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ a len : ℕ,
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (quarticSixMain W.eval w.1
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star ((((E b).selectedExpansion ((i, i), (i, i)) v).test z).eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star (((F.selectedExpansion v w).test z').eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_quartic_multilinear_intervals_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, r, u, hr, hrq, hu, huq, E, F,
    i, b, v, z, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let K := Σ w : QuarticSixFactorIndex (Fin W.outputDim), Fin (F.selectedExpansion v w).count
  let R (t : (ZMod N × ZMod N) × ZMod N) (_ : Unit) (c : K) : Prop :=
    ∃ a len : ℕ,
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
        ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          multiplicativeDerivative
            (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
            star (quarticSixMain W.eval c.1.1
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
            star ((((E b).selectedExpansion ((i, i), (i, i)) v).test z).eval
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
            star (((F.selectedExpansion v c.1).test c.2).eval
              ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖
  have hchoice : ∀ t ∈ Q, ∀ j, ∃ c, R t j c := by
    intro t ht _
    obtain ⟨a, len, hlen, hend, hshort, hvol, w, z', hcor⟩ := hQcorr t ht
    exact ⟨⟨w, z'⟩, a, len, hlen, hend, hshort, hvol, hcor⟩
  have hcount : (Fintype.card K : ℝ) ≤ Real.exp (2 * u) := by
    change (Fintype.card (Σ w : QuarticSixFactorIndex (Fin W.outputDim),
      Fin (F.selectedExpansion v w).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _w : QuarticSixFactorIndex (Fin W.outputDim), Real.exp u := by
        apply Finset.sum_le_sum
        intro w _
        simpa only [Fintype.card_fin] using (F.selectedExpansion v w).count_bound
      _ = (Fintype.card (QuarticSixFactorIndex (Fin W.outputDim)) : ℝ) * Real.exp u := by simp
      _ ≤ Real.exp u * Real.exp u :=
        mul_le_mul_of_nonneg_right F.right_dimension (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  obtain ⟨c, S, _, hS, hSdense, hfixed⟩ := exists_large_fixed_choices Q hQ R hchoice hcount
  have hsize : Real.exp (-(2 * u)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC,
    r, u, hr, hrq.trans hqC, hu, huq.trans hqC, E, F, i, b, v, z,
    (c ()).1, (c ()).2, S, hS, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + 2 * u)) * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-(2 * u)) * (Real.exp (-q) * (N : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * u)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨a, len, hlen, hend, hshort, hvol, hcor⟩ := hfixed t ht ()
    exact ⟨a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hcor⟩

theorem exists_quartic_fixed_multilinear_intervals :
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
        ∃ r u : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧ 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ E : ∀ b : Fin 3 → Fin 3, NativeIntegerVectorEquivalence 3 r
          (M.mixedSecondDifferenceWithShift (doubleDifferenceCarryShift N b))
          (M.mixedSecondDifferenceWithShift 0),
        ∃ F : NativeIntegerVectorEquivalence 3 u (M.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval),
        ∃ (i : Fin M.outputDim) (b : Fin 3 → Fin 3)
          (v : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
          (z : Fin ((E b).selectedExpansion ((i, i), (i, i)) v).count),
        ∃ (w : QuarticSixFactorIndex (Fin W.outputDim)) (z' : Fin (F.selectedExpansion v w).count),
        ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
          ∀ t ∈ Q, ∃ a len : ℕ,
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                multiplicativeDerivative
                  (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                  star (quarticSixMain W.eval w.1
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star ((((E b).selectedExpansion ((i, i), (i, i)) v).test z).eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  star (((F.selectedExpansion v w).test z').eval
                    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_fixed_multilinear_intervals_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_quartic_separated_intervals_with_mixed :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
            Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
            ∀ t ∈ Q, ∃ a len : ℕ,
              0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
              Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  (multiplicativeDerivative
                    (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                    star (quarticSixMain W.eval out
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])) *
                    ∏ i, A i ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]‖ := by
  obtain ⟨a, _, hinterval⟩ := exists_quartic_fixed_multilinear_intervals_with_mixed
  obtain ⟨b, _, habsorb⟩ := exists_absorb_pair_missing_coordinate_errors 3
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r + 2 ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, r₀, u, hr₀, hr₀q, hu, huq, E, F,
    i, branch, v, z, w, z', Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let T := ((E branch).selectedExpansion ((i, i), (i, i)) v).test z
  let U := (F.selectedExpansion v w).test z'
  have hT : T.ComplexityLE q := (((E branch).selectedExpansion ((i, i), (i, i)) v).complexity z).mono hr₀q
  have hU : U.ComplexityLE q := ((F.selectedExpansion v w).complexity z').mono huq
  have hdata (t : Q) := hQcorr t.val t.property
  choose start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) (n : ℤ) : Fin 4 → ℤ :=
    ![(t.val.1.2.val : ℤ), n, (t.val.1.1.val : ℤ), (t.val.2.val : ℤ)]
  let signal (t : Q) (n : ℤ) :=
    multiplicativeDerivative
      (multiplicativeDerivative (multiplicativeDerivative f t.val.1.1) t.val.2) t.val.1.2 (n : ZMod N) *
      star (quarticSixMain W.eval w.1 (sample t n))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one _
        (multiplicativeDerivative_norm_le_one _
          (multiplicativeDerivative_norm_le_one f hf t.val.1.1) t.val.2) t.val.1.2 _)).trans ?_
    rw [quarticSixMain, norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => W.norm_eval _ _)
  obtain ⟨A, hA, hAind, S, _, hS, hSdense, hScor⟩ :=
    habsorb T U hT hU Finset.univ Finset.univ_nonempty I (fun t _ => hI t)
      sample signal (fun t _ n _ => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ (ZMod N × ZMod N) × ZMod N := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-r) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC,
    F.mono (huq.trans hqC), w.1, A, hA, hAind, Q', hQ', ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + r)) * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-r) * (Real.exp (-q) * (N : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'),
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hScor t' ht')⟩

theorem exists_quartic_separated_intervals :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
            Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
            ∀ t ∈ Q, ∃ a len : ℕ,
              0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
              Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  (multiplicativeDerivative
                    (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                    star (quarticSixMain W.eval out
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])) *
                    ∏ i, A i ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_separated_intervals_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_common_interval_with_mixed :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  (multiplicativeDerivative
                    (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                    star (quarticSixMain W.eval out
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])) *
                    ∏ i, A i ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]‖ := by
  obtain ⟨c, _, hseparated⟩ := exists_quartic_separated_intervals_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (5 * P + 12)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 5 * q + 12 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hgridC : 2 * q + 8 ≤ (p + C) ^ C := by linarith
  have hcC : q + 1 ≤ (p + C) ^ C := by linarith
  have hdC : 5 * q + 10 ≤ (p + C) ^ C := by linarith
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, out, A, hA, hAind, Q, hQ, hQdense, hQcorr⟩ :=
    hseparated hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  have hdata (t : Q) := hQcorr t.val t.property
  choose start len hlen hend hshort hvol hcor using hdata
  let signal (t : Q) (n : ℤ) :=
    (multiplicativeDerivative
      (multiplicativeDerivative (multiplicativeDerivative f t.val.1.1) t.val.2) t.val.1.2 (n : ZMod N) *
      star (quarticSixMain W.eval out
        ![(t.val.1.2.val : ℤ), n, (t.val.1.1.val : ℤ), (t.val.2.val : ℤ)])) *
      ∏ i, A i ![(t.val.1.2.val : ℤ), n, (t.val.1.1.val : ℤ), (t.val.2.val : ℤ)]
  let : Nonempty Q := hQ.to_subtype
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) (multiplicativeDerivative_norm_le_one _
        (multiplicativeDerivative_norm_le_one _
          (multiplicativeDerivative_norm_le_one f hf t.val.1.1) t.val.2) t.val.1.2 _)).trans
        (W.quarticSixMain_norm out _))).trans ?_
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  obtain ⟨S, _, hS, hSdense, a, d, hd, had, hshortd, hvold, hScor⟩ :=
    exists_common_integer_interval hq ((Real.exp_le_exp.mpr hgridC).trans hN)
      Finset.univ Finset.univ_nonempty start len (fun t _ => hend t) (fun t _ => hshort t)
      (fun t _ => (le_div_iff₀ hNpos).mp (hvol t)) signal
      (fun t _ n => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ (ZMod N × ZMod N) × ZMod N := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-(4 * q + 10)) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC,
    out, A, hA, hAind, a, d, hd, had, hshortd, ?_, Q', hQ', ?_, ?_⟩
  · apply (le_div_iff₀ hNpos).mpr
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcC)) hNpos.le).trans hvold
  · calc
      _ ≤ Real.exp (-(5 * q + 10)) * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdC)) (by positivity)
      _ = Real.exp (-(4 * q + 10)) * (Real.exp (-q) * (N : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(4 * q + 10)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact (Real.exp_le_exp.mpr (neg_le_neg hcC)).trans (hScor t' ht')

theorem exists_quartic_common_interval :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ Q : Finset ((ZMod N × ZMod N) × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  (multiplicativeDerivative
                    (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
                    star (quarticSixMain W.eval out
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)])) *
                    ∏ i, A i ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]‖ := by
  obtain ⟨C, hC, h⟩ := exists_quartic_common_interval_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_positive_correlation_with_mixed :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              (𝔼 t : (ZMod N × ZMod N) × ZMod N,
                𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  star (f ((n + (t.1.2.val : ℤ) + (t.1.1.val : ℤ) + (t.2.val : ℤ) : ℤ) : ZMod N)) *
                    star (quarticSixMain W.eval out
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                    ∏ i, A i ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]).re := by
  obtain ⟨c, _, hcommon⟩ := exists_quartic_common_interval_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have htwo : 2 * q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, out, A₀, hA₀, hA₀ind,
    a, len, hlen, hend, hshort, hvol, Q, _, hQdense, hQcorr⟩ :=
    hcommon hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  obtain ⟨A, hA, hAind, habsorb⟩ := exists_quartic_diagonal_weights f hf A₀ hA₀ hA₀ind
  let sample (t : (ZMod N × ZMod N) × ZMod N) (n : ℤ) : Fin 4 → ℤ :=
    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]
  let row (t : (ZMod N × ZMod N) × ZMod N) (n : ℤ) :=
    star (f ((n + (t.1.2.val : ℤ) + (t.1.1.val : ℤ) + (t.2.val : ℤ) : ℤ) : ZMod N)) *
      star (quarticSixMain W.eval out (sample t n)) * ∏ i, A i (sample t n)
  have hrow : ∀ t ∈ Q, Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), row t n‖ := by
    intro t ht
    have heq (n : ℤ) :
        (multiplicativeDerivative
          (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
          star (quarticSixMain W.eval out (sample t n))) * ∏ i, A₀ i (sample t n) = row t n := by
      simpa only [row, sample, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        Int.cast_natCast, ZMod.natCast_zmod_val] using
          habsorb (sample t n) (star (quarticSixMain W.eval out (sample t n)))
    have H := hQcorr t ht
    change Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
      (multiplicativeDerivative
        (multiplicativeDerivative (multiplicativeDerivative f t.1.1) t.2) t.1.2 (n : ZMod N) *
        star (quarticSixMain W.eval out (sample t n))) * ∏ i, A₀ i (sample t n)‖ at H
    simpa only [heq] using H
  have hdensity : Real.exp (-q) * Fintype.card ((ZMod N × ZMod N) × ZMod N) ≤ (Q.card : ℝ) := by
    have hcard : (Fintype.card ((ZMod N × ZMod N) × ZMod N) : ℝ) = (N : ℝ) ^ 3 := by
      simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul]
      ring
    rw [hcard]
    exact hQdense
  obtain ⟨w, hw, _, hpositive⟩ := exists_dense_row_phase_alignment Q
    (Finset.Ico (a : ℤ) (a + len)) row (Real.exp_nonneg (-q)) hdensity hrow
  let phase (x : Fin 4 → ℤ) := w (((x 2 : ZMod N), (x 0 : ZMod N)), (x 3 : ZMod N))
  let B (i : Fin 4) (x : Fin 4 → ℤ) := if i = 1 then phase x * A i x else A i x
  have hB : ∀ i x, ‖B i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = 1
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw _)).trans (hA _ _)
    · simpa only [B, hi, ite_false] using hA i x
  have hBind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y := by
    intro i x y hxy
    by_cases hi : i = 1
    · subst i
      simp only [B, ite_true]
      rw [hAind 1 x y hxy]
      dsimp only [phase]
      rw [hxy 2 (by decide), hxy 0 (by decide), hxy 3 (by decide)]
    · simpa only [B, hi, ite_false] using hAind i x y hxy
  have hphase (t : (ZMod N × ZMod N) × ZMod N) (n : ℤ) : phase (sample t n) = w t := by
    simp [phase, sample]
  have hprod (x : Fin 4 → ℤ) : (∏ i, B i x) = phase x * ∏ i, A i x := by
    simp [B, Fin.prod_univ_four]
    ring
  have hpoint (t : (ZMod N × ZMod N) × ZMod N) (n : ℤ) :
      star (f ((n + (t.1.2.val : ℤ) + (t.1.1.val : ℤ) + (t.2.val : ℤ) : ℤ) : ZMod N)) *
        star (quarticSixMain W.eval out (sample t n)) * ∏ i, B i (sample t n) = w t * row t n := by
    rw [hprod, hphase]
    dsimp only [row]
    ring
  have hscore : Real.exp (-(2 * q)) ≤
      (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), w t * row t n).re := by
    have heq : Real.exp (-(2 * q)) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hpositive
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC,
    out, B, hB, hBind, a, len, hlen, hend, hshort,
    (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol, ?_⟩
  change Real.exp (-((p + C) ^ C)) ≤
    (𝔼 t : (ZMod N × ZMod N) × ZMod N, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
      star (f ((n + (t.1.2.val : ℤ) + (t.1.1.val : ℤ) + (t.2.val : ℤ) : ℤ) : ZMod N)) *
        star (quarticSixMain W.eval out (sample t n)) * ∏ i, B i (sample t n)).re
  simpa only [hpoint] using (Real.exp_le_exp.mpr (neg_le_neg htwo)).trans hscore

theorem exists_quartic_positive_correlation :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              (𝔼 t : (ZMod N × ZMod N) × ZMod N,
                𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  star (f ((n + (t.1.2.val : ℤ) + (t.1.1.val : ℤ) + (t.2.val : ℤ) : ℤ) : ZMod N)) *
                    star (quarticSixMain W.eval out
                      ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                    ∏ i, A i ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]).re := by
  obtain ⟨C, hC, h⟩ := exists_quartic_positive_correlation_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_cyclic_positive_correlation_with_mixed :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            (∀ x, (x 1 : ZMod N) ∉ cyclicInterval (a : ZMod N) len → A 0 x = 0) ∧
            Real.exp (-((p + C) ^ C)) ≤
              (𝔼 t : (ZMod N × ZMod N) × ZMod N, 𝔼 n : ZMod N,
                star (f (n + t.1.2 + t.1.1 + t.2)) *
                  star (quarticSixMain W.eval out
                    ![(t.1.2.val : ℤ), (n.val : ℤ), (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  ∏ i, A i ![(t.1.2.val : ℤ), (n.val : ℤ), (t.1.1.val : ℤ), (t.2.val : ℤ)]).re := by
  obtain ⟨c, _, hinterval⟩ := exists_quartic_positive_correlation_with_mixed
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have htwo : 2 * q ≤ (p + C) ^ C := by linarith
  obtain ⟨M, hret, W, hdim, hsymm, hdiag, E, out, A, hA, hAind,
    a, len, hlen, hend, hshort, hvol, hpositive⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let I := cyclicInterval (a : ZMod N) len
  let B (i : Fin 4) (x : Fin 4 → ℤ) :=
    if i = 0 then A i x * finiteIndicator I (x 1 : ZMod N) else A i x
  let sample (t : (ZMod N × ZMod N) × ZMod N) (n : ℤ) : Fin 4 → ℤ :=
    ![(t.1.2.val : ℤ), n, (t.1.1.val : ℤ), (t.2.val : ℤ)]
  let F (t : (ZMod N × ZMod N) × ZMod N) (n : ℤ) :=
    star (f ((n + (t.1.2.val : ℤ) + (t.1.1.val : ℤ) + (t.2.val : ℤ) : ℤ) : ZMod N)) *
      star (quarticSixMain W.eval out (sample t n)) * ∏ i, A i (sample t n)
  let G (t : (ZMod N × ZMod N) × ZMod N) (n : ZMod N) :=
    star (f (n + t.1.2 + t.1.1 + t.2)) *
      star (quarticSixMain W.eval out (sample t (n.val : ℤ))) * ∏ i, B i (sample t (n.val : ℤ))
  have hprod (x : Fin 4 → ℤ) :
      (∏ i, B i x) = finiteIndicator I (x 1 : ZMod N) * ∏ i, A i x := by
    simp [B, Fin.prod_univ_four]
    ring
  have hrow (t : (ZMod N × ZMod N) × ZMod N) : (𝔼 n, G t n) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F t n) := by
    calc
      _ = 𝔼 n : ZMod N, finiteIndicator I n * F t (n.val : ℤ) := by
        apply Finset.expect_congr rfl
        intro n _
        simp only [G, F, hprod, sample, Matrix.cons_val_one, Matrix.cons_val_zero,
          Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
        ring
      _ = _ := cyclicInterval_zeroExtension_average a len hend hshort (F t)
  have hmean : (𝔼 t, 𝔼 n, G t n).re =
      (len : ℝ) / N * (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F t n).re := by
    simp_rw [hrow]
    rw [← Finset.mul_expect]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hB : ∀ i x, ‖B i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = 0
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hA _ _)).trans
        (finiteIndicator_norm_le_one I _)
    · simpa only [B, hi, ite_false] using hA i x
  have hBind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y := by
    intro i x y hxy
    by_cases hi : i = 0
    · subst i
      simp only [B, ite_true]
      rw [hAind 0 x y hxy, hxy 1 (by decide)]
    · simpa only [B, hi, ite_false] using hAind i x y hxy
  refine ⟨M.mono hqC, hret.mono hqC, W.mono hqC, hdim, hsymm, hdiag.mono hqC, E.mono hqC,
    out, B, hB, hBind, a, len, hlen, hend, hshort,
    (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol, ?_, ?_⟩
  · intro x hx
    simp only [B, ite_true, I, finiteIndicator, hx, ite_false, mul_zero]
  · change Real.exp (-((p + C) ^ C)) ≤ (𝔼 t, 𝔼 n, G t n).re
    rw [hmean]
    calc
      _ ≤ Real.exp (-(2 * q)) := Real.exp_le_exp.mpr (neg_le_neg htwo)
      _ = Real.exp (-q) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hvol hpositive (Real.exp_nonneg _) (by positivity)

theorem exists_quartic_cyclic_positive_correlation :
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
        ∃ (out : Fin 6 → Fin W.outputDim) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
          (∀ i x, ‖A i x‖ ≤ 1) ∧
          (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
          ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            (∀ x, (x 1 : ZMod N) ∉ cyclicInterval (a : ZMod N) len → A 0 x = 0) ∧
            Real.exp (-((p + C) ^ C)) ≤
              (𝔼 t : (ZMod N × ZMod N) × ZMod N, 𝔼 n : ZMod N,
                star (f (n + t.1.2 + t.1.1 + t.2)) *
                  star (quarticSixMain W.eval out
                    ![(t.1.2.val : ℤ), (n.val : ℤ), (t.1.1.val : ℤ), (t.2.val : ℤ)]) *
                  ∏ i, A i ![(t.1.2.val : ℤ), (n.val : ℤ), (t.1.1.val : ℤ), (t.2.val : ℤ)]).re := by
  obtain ⟨C, hC, h⟩ := exists_quartic_cyclic_positive_correlation_with_mixed
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨M, _hret, hM⟩ := h hp hN f hf hGowers
  exact ⟨M, hM⟩

end Erdos3

end

end OAI
