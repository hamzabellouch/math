import OAI.Combinatorics.Progressions.Estimates.CubicRootPermutation
import OAI.Combinatorics.Progressions.Estimates.QuarticRootExchange

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def thirdDilationExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    ((W.rationalDilation (1 / 3)).eval a (cubicTrilinearInput (x 0) (x 1) (x 1)))
    ((W.rationalDilation (1 / 3)).eval b (cubicTrilinearInput (x 1) (x 0) (x 1)))
    (fun i => W.eval i (cubicTrilinearInput (x 0 / 3) (x 1 / 3) (x 1 / 3)))
    (fun j => W.eval j (cubicTrilinearInput (x 1 / 3) (x 0 / 3) (x 1 / 3)))
    (fun i j => G i j (fun k => x k / 3))

theorem thirdDilationExchangeCorrection_pointwise_error
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation (1 / 3)).eval a (cubicTrilinearInput (x 0) (x 1) (x 1)) *
        star ((W.rationalDilation (1 / 3)).eval b (cubicTrilinearInput (x 1) (x 0) (x 1))) -
      W.thirdDilationExchangeCorrection G a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.eval ij.1 (cubicTrilinearInput (x 0 / 3) (x 1 / 3) (x 1 / 3)) *
            star (W.eval ij.2 (cubicTrilinearInput (x 1 / 3) (x 0 / 3) (x 1 / 3))) -
          G ij.1 ij.2 (fun k => x k / 3)‖ := by
  exact norm_sub_complexCrossContraction_le_sum _ _ _ _ _
    ((W.rationalDilation (1 / 3)).norm_eval _ _) ((W.rationalDilation (1 / 3)).norm_eval _ _)
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)

theorem thirdDilationExchangeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval j (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation (1 / 3)).eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star ((W.rationalDilation (1 / 3)).eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        W.thirdDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      9 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.thirdDilationExchangeCorrection_pointwise_error G a b
      (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.eval ij.1 (cubicTrilinearInput (((x 0).val : ℤ) / 3) (((x 1).val : ℤ) / 3)
              (((x 1).val : ℤ) / 3)) *
            star (W.eval ij.2 (cubicTrilinearInput (((x 1).val : ℤ) / 3) (((x 0).val : ℤ) / 3)
              (((x 1).val : ℤ) / 3))) -
          G ij.1 ij.2 (fun k => ((x k).val : ℤ) / 3)‖) ≤ 9 * ε := by
    have h := expect_pair_cyclicThird_le (fun x : Fin 2 → ZMod N =>
      ‖W.eval ij.1 (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval ij.2 (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicThird_val, Int.natCast_ediv, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr ij.1 ij.2) (by norm_num))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, 9 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem thirdDilationExchangeCorrection_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.thirdDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold thirdDilationExchangeCorrection complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      · have h := hG ij.1 ij.2 (fun k => cyclicThird (x k))
        simpa only [cyclicThird_val, Int.natCast_ediv, Nat.cast_ofNat] using h
      · rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
        refine (mul_le_of_le_one_left
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
        · exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 3)).norm_eval _ _)).trans (W.norm_eval _ _)
        · exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 3)).norm_eval _ _)).trans (W.norm_eval _ _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

theorem exists_thirdDilationExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
        (W.thirdDilationExchangeCorrection G a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_cubic_third_dilation_pattern_equivalence
  obtain ⟨B, _, hthird⟩ := NativeIntegerExpansion.exists_thirds_expansion
  obtain ⟨D, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) B
  have hF (i j : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 t
      (fun x => G i j (fun k => x k / 3))) :=
    ⟨(Classical.choice (hthird hq (Classical.choice (hG i j)))).mono hBt⟩
  have H := hcontract (fun i j x => G i j (fun k => x k / 3)) ht
    ((hcompare W 0 1 1).mono hAt) ((hcompare W 1 0 1).mono hAt) hF a b
  have hcost : (t + D) ^ D ≤ (p + q + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨(Classical.choice H).mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicTensorExchangeCorrection (n : ℕ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) : ℂ :=
  ∏ k : Fin n, G ((tensorIndexEquiv W.outputDim n).symm a k)
    ((tensorIndexEquiv W.outputDim n).symm b k) x

theorem cubicTensorExchange_kernel (n : ℕ) (a b : Fin (W.outputDim ^ n)) (h m : ℤ) :
    (W.tensorPower n).eval a (cubicTrilinearInput h m m) *
        star ((W.tensorPower n).eval b (cubicTrilinearInput m h m)) =
      ∏ k : Fin n, W.eval ((tensorIndexEquiv W.outputDim n).symm a k) (cubicTrilinearInput h m m) *
        star (W.eval ((tensorIndexEquiv W.outputDim n).symm b k) (cubicTrilinearInput m h m)) := by
  simp only [tensorPower_eval, star_prod, Finset.prod_mul_distrib]

theorem cubicTensorExchangeCorrection_norm (n : ℕ) {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ZMod N) :
    ‖W.cubicTensorExchangeCorrection n G a b (fun k => ((x k).val : ℤ))‖ ≤ B ^ n := by
  rw [cubicTensorExchangeCorrection, norm_prod]
  calc
    _ ≤ ∏ _ : Fin n, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hG _ _ x)
    _ = _ := by simp

theorem cubicTensorExchangeCorrection_mean_error (n : ℕ) {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval j (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower n).eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star ((W.tensorPower n).eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        W.cubicTensorExchangeCorrection n G a b (fun k => ((x k).val : ℤ))‖) ≤ B ^ n * (n * ε) := by
  let i := (tensorIndexEquiv W.outputDim n).symm a
  let j := (tensorIndexEquiv W.outputDim n).symm b
  have h := mean_prod_error_le
    (fun k (x : Fin 2 → ZMod N) =>
      W.eval (i k) (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
        star (W.eval (j k) (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)))
    (fun k (x : Fin 2 → ZMod N) => G (i k) (j k) (fun l => ((x l).val : ℤ))) hB
    (fun k x => (by
      rw [norm_mul, norm_star]
      exact ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
        (W.norm_eval _ _)).trans hB))
    (fun _ x => hG _ _ x) (fun k => herr (i k) (j k))
  simpa only [Fintype.card_fin, cubicTensorExchange_kernel, cubicTensorExchangeCorrection, i, j] using h

theorem exists_cubicTensorExchangeCorrection_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((q + C) ^ C)
        (W.cubicTensorExchangeCorrection n G a b)) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  exact hprod _ hq (fun _ => hG _ _)

noncomputable def cubicRootExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (1 / 3)).cubicTensorExchangeCorrection 9 (W.thirdDilationExchangeCorrection G)

theorem cubicRootExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (a b : Fin W.cubicRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicRootExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 18 := by
  have hH (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.thirdDilationExchangeCorrection G i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.thirdDilationExchangeCorrection_norm G hG i j x
  simpa only [cubicRootExchangeCorrection, ← pow_mul] using
    (W.rationalDilation (1 / 3)).cubicTensorExchangeCorrection_norm 9
      (W.thirdDilationExchangeCorrection G) hH a b x

theorem cubicRootExchangeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval j (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin W.cubicRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRoot.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.cubicRoot.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        W.cubicRootExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      81 * (W.outputDim : ℝ) ^ 20 * ε := by
  have hdNat : 1 ≤ W.outputDim := W.output_pos
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast hdNat
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hH (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.thirdDilationExchangeCorrection G i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.thirdDilationExchangeCorrection_norm G hG i j x
  have h := (W.rationalDilation (1 / 3)).cubicTensorExchangeCorrection_mean_error 9
    (W.thirdDilationExchangeCorrection G) hB hH
    (W.thirdDilationExchangeCorrection_mean_error G herr) a b
  exact h.trans_eq (by norm_num only [Nat.cast_ofNat]; ring)

theorem exists_cubicRootExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + q + C) ^ C)
        (W.cubicRootExchangeCorrection G a b)) := by
  obtain ⟨A, _, hthird⟩ := exists_thirdDilationExchangeCorrection_expansion
  obtain ⟨B, _, htensor⟩ := exists_cubicTensorExchangeCorrection_expansion 9
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := htensor (W.rationalDilation (1 / 3)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.thirdDilationExchangeCorrection G) (hthird W hq G hG) a b
  have hcost : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
