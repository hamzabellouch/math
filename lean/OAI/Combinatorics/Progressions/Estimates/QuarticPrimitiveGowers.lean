import OAI.Combinatorics.Progressions.Dynamics.QuarticCyclicErrorBudget
import OAI.Combinatorics.Progressions.Estimates.CubicResidualCrossGowers
import OAI.Combinatorics.Progressions.Estimates.QuarticFrozenRows
import OAI.Combinatorics.Progressions.Estimates.QuarticPairPartitionedModel

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_corner_exchange_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2), NativeIntegerVectorEquivalence 3 r
        (fun i (x : Fin 2 → ℤ) => W.eval i (quarticSampledInput π x))
        (fun i x => W.eval i (quarticSampledInput (quarticPermuteSample e π) x))) →
      ∀ a b v, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((q + r + C) ^ C)
        (W.quarticCornerExchangeFactor G a b v)) := by
  obtain ⟨A, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b v
  let t := q + r
  have ht : 0 ≤ t := add_nonneg hq hr
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hsum : t + (t + A) ^ A ≤ (q + r + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have htC : t ≤ (q + r + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hAC : (t + A) ^ A ≤ (q + r + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  by_cases hv : v.val 0 = 1
  · have hcanon := quarticCanonicalSample_of_first_one v.val hv
    obtain ⟨F⟩ := ((hperm (quarticWordPermutation (quarticTailSortWord v.val))
      (quarticCornerSample v.val)).mono hrt).expansion (a v) (b v)
    have heq : (fun x => W.eval (a v) (quarticSampledInput (quarticCornerSample v.val) x) *
        star (W.eval (b v) (quarticSampledInput
          (quarticPermuteSample (quarticWordPermutation (quarticTailSortWord v.val))
            (quarticCornerSample v.val)) x))) = W.quarticCornerExchangeFactor G a b v := by
      funext x
      simp only [quarticCornerExchangeFactor, ite_eq_left hv, quarticRawCornerFactor,
        quarticCornerSample_input, hcanon]
    exact ⟨heq ▸ F.mono htC⟩
  · have hv0 := quarticCorner_first_zero_of_ne_one v.val hv
    have hcanon := quarticCanonicalSample_of_first_zero v hv0
    have Eleft : NativeIntegerVectorEquivalence 3 t
        (fun i (x : Fin 2 → ℤ) => W.eval i (quarticDiagonalCorner v.val x))
        (fun i x => W.eval i (quarticSampledInput (quarticPreExchangeSample v.val) x)) := by
      simpa only [quarticCornerSample_input, quarticPreExchangeSample] using
        (hperm (quarticWordPermutation (quarticHeadWord v.val)) (quarticCornerSample v.val)).mono hrt
    have Eright : NativeIntegerVectorEquivalence 3 t
        (fun i (x : Fin 2 → ℤ) => W.eval i (quarticSampledInput (quarticCanonicalSample v.val) x))
        (fun i x => W.eval i (quarticSampledInput (quarticSwapSample (quarticPreExchangeSample v.val)) x)) := by
      rw [hcanon]
      exact ((hperm (quarticWordPermutation (quarticPostExchangeWord v.val))
        (quarticSwapSample (quarticPreExchangeSample v.val))).mono hrt).symm
    have H := hcontract (fun i j x => G (quarticPreExchangeSample v.val) i j x) ht Eleft Eright
      (fun i j => ⟨(Classical.choice (hG _ i j)).mono hqt⟩) (a v) (b v)
    have heq : (fun x => complexCrossContraction
        (W.eval (a v) (quarticDiagonalCorner v.val x))
        (W.eval (b v) (quarticSampledInput (quarticCanonicalSample v.val) x))
        (fun i => W.eval i (quarticSampledInput (quarticPreExchangeSample v.val) x))
        (fun j => W.eval j (quarticSampledInput (quarticSwapSample (quarticPreExchangeSample v.val)) x))
        (fun i j => G (quarticPreExchangeSample v.val) i j x)) = W.quarticCornerExchangeFactor G a b v := by
      funext x
      simp only [quarticCornerExchangeFactor, ite_eq_right hv]
    exact ⟨heq ▸ (Classical.choice H).mono hAC⟩

theorem exists_quartic_fifteen_exchange_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2), NativeIntegerVectorEquivalence 3 r
        (fun i (x : Fin 2 → ℤ) => W.eval i (quarticSampledInput π x))
        (fun i x => W.eval i (quarticSampledInput (quarticPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((q + r + C) ^ C)
        (W.quarticFifteenExchangeProduct G a b)) := by
  obtain ⟨A, _, hfactor⟩ := exists_quartic_corner_exchange_expansion
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 15
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  let e : Fin 15 ≃ QuarticNonconstantCorner := (Fintype.equivFinOfCardEq quarticNonconstantCorner_card).symm
  obtain ⟨F⟩ := hprod (fun k => W.quarticCornerExchangeFactor G a b (e k))
    (by positivity : 0 ≤ (q + r + A) ^ A)
    (fun k => hfactor W G hq hr hG hperm a b (e k))
  have hcost : ((q + r + A) ^ A + B) ^ B ≤ (q + r + C) ^ C := by
    simpa [X, T, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have heq : (fun x => star (∏ k : Fin 15, W.quarticCornerExchangeFactor G a b (e k) x)) =
      W.quarticFifteenExchangeProduct G a b := by
    funext x
    exact congrArg star (e.prod_comp (fun v => W.quarticCornerExchangeFactor G a b v x))
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticPermutedDiagonalCorrection
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (b : QuarticNonconstantCorner → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ c : QuarticNonconstantCorner → Fin W.outputDim,
    (W.quarticDiagonalDerivative a x * star (W.quarticMixedFifteen c x)) *
      W.quarticFifteenExchangeProduct G c b x

theorem quarticPermutedDiagonalCorrection_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π a b (x : Fin 2 → ZMod N), ‖G π a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a : Fin W.outputDim × Fin W.outputDim) (b : QuarticNonconstantCorner → Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖W.quarticPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 15 * ((W.outputDim : ℝ) ^ 2 * B) ^ 15 := by
  unfold quarticPermutedDiagonalCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : QuarticNonconstantCorner → Fin W.outputDim, ((W.outputDim : ℝ) ^ 2 * B) ^ 15 := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
        (W.quarticFifteenExchangeProduct_norm G hB hG c b x)
      rw [norm_mul, norm_star]
      exact (mul_le_mul_of_nonneg_right (W.quarticDiagonalDerivative_norm _ _)
        (norm_nonneg _)).trans (by simpa only [one_mul] using W.quarticMixedFifteen_norm _ _)
    _ = _ := by simp

theorem quarticPermutedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π a b (x : Fin 2 → ZMod N), ‖G π a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim) (b : QuarticNonconstantCorner → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
        W.quarticPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 15 * (((W.outputDim : ℝ) ^ 2 * B) ^ 15 * (15 * ((W.outputDim : ℝ) ^ 2 * ε))) := by
  have hid (x : Fin 2 → ℤ) :
      W.quarticDiagonalDerivative a x * star (W.quarticSymmetricFifteen b x) =
        ∑ c : QuarticNonconstantCorner → Fin W.outputDim,
          (W.quarticDiagonalDerivative a x * star (W.quarticMixedFifteen c x)) *
            (W.quarticMixedFifteen c x * star (W.quarticSymmetricFifteen b x)) := by
    calc
      _ = ∑ c, ((W.quarticDiagonalDerivative a x * star (W.quarticSymmetricFifteen b x)) *
          star (W.quarticMixedFifteen c x)) * W.quarticMixedFifteen c x :=
        complex_unit_vector_resolution _ (W.quarticMixedFifteen_unit x) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        ring
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.quarticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
        W.quarticPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ c : QuarticNonconstantCorner → Fin W.outputDim,
        ‖W.quarticMixedFifteen c (fun z => ((x z).val : ℤ)) *
            star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
          W.quarticFifteenExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ := by
    rw [hid, quarticPermutedDiagonalCorrection, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [← mul_sub, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (W.quarticDiagonalDerivative_norm _ _)
      (norm_nonneg _)).trans (by simpa only [one_mul] using W.quarticMixedFifteen_norm _ _)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ c : QuarticNonconstantCorner → Fin W.outputDim,
        ‖W.quarticMixedFifteen c (fun z => ((x z).val : ℤ)) *
            star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
          W.quarticFifteenExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ c : QuarticNonconstantCorner → Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
        ‖W.quarticMixedFifteen c (fun z => ((x z).val : ℤ)) *
            star (W.quarticSymmetricFifteen b (fun z => ((x z).val : ℤ))) -
          W.quarticFifteenExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : QuarticNonconstantCorner → Fin W.outputDim,
        ((W.outputDim : ℝ) ^ 2 * B) ^ 15 * (15 * ((W.outputDim : ℝ) ^ 2 * ε)) :=
      Finset.sum_le_sum (fun c _ => W.quarticFifteenExchangeProduct_mean_error G hB hε hG herr c b)
    _ = _ := by simp

theorem exists_quartic_permuted_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin 3)) (π : Fin 4 → Fin 2), NativeIntegerVectorEquivalence 3 r
        (fun i (x : Fin 2 → ℤ) => W.eval i (quarticSampledInput π x))
        (fun i x => W.eval i (quarticSampledInput (quarticPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + r + C) ^ C)
        (W.quarticPermutedDiagonalCorrection G a b)) := by
  obtain ⟨A, _, hderivative⟩ := exists_quartic_diagonal_derivative_equivalence
  obtain ⟨B, _, hseven⟩ := exists_quartic_fifteen_exchange_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D + 15 * X)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + r + A) ^ A + (p + q + r + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + r + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hterm (c : QuarticNonconstantCorner → Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((t + D) ^ D)
        (fun x => (W.quarticDiagonalDerivative a x * star (W.quarticMixedFifteen c x)) *
          W.quarticFifteenExchangeProduct G c b x)) := by
    exact hmul ht (Classical.choice (((hderivative W).mono hAt).expansion a c))
      ((Classical.choice (hseven W G hq hr hG hperm c b)).mono hBt)
  have hdim : (Fintype.card (QuarticNonconstantCorner → Fin W.outputDim) : ℝ) ≤ Real.exp (15 * p) := by
    simp only [Fintype.card_fun, quarticNonconstantCorner_card, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound 15).trans_eq
      (Real.exp_nat_mul p 15).symm
  have hcoeff : (∑ _ : QuarticNonconstantCorner → Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (15 * p) := by
    simpa using hdim
  have H := NativeIntegerExpansion.weightedSum (fun c => Classical.choice (hterm c))
    (fun _ => 1) (by positivity : 0 ≤ 15 * p) hdim hcoeff
  have hcost : (t + D) ^ D + 15 * p ≤ (p + q + r + C) ^ C := by
    have hb : (t + D) ^ D + 15 * (p + q + r) ≤ (p + q + r + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q + r) (by positivity)
    linarith
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + r + C) ^ C)
    (fun x => ∑ c : QuarticNonconstantCorner → Fin W.outputDim,
      (W.quarticDiagonalDerivative a x * star (W.quarticMixedFifteen c x)) *
        W.quarticFifteenExchangeProduct G c b x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticRootFifteenCorrection
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.quarticRoot.quarticPermutedDiagonalCorrection (W.quarticRootExchangeCorrection G)

theorem quarticRootFifteenCorrection_norm {N : ℕ} [NeZero N]
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim)
    (b : QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quarticRootFifteenCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 4800 := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 128 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd 128
  have hdim : (W.quarticRoot.outputDim : ℝ) = (W.outputDim : ℝ) ^ 64 := by
    change ((W.outputDim ^ 64 : ℕ) : ℝ) = _
    exact Nat.cast_pow _ _
  have h := W.quarticRoot.quarticPermutedDiagonalCorrection_norm
    (W.quarticRootExchangeCorrection G) hB (W.quarticRootExchangeCorrection_norm G hG) a b x
  apply h.trans_eq
  rw [hdim]
  simp only [← pow_mul, ← pow_add]

theorem quarticRootFifteenCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim)
    (b : QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRoot.quarticDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.quarticRoot.quarticSymmetricFifteen b (fun k => ((x k).val : ℤ))) -
        W.quarticRootFifteenCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      15360 * (W.outputDim : ℝ) ^ 5058 * ε := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 128 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd 128
  have hdim : (W.quarticRoot.outputDim : ℝ) = (W.outputDim : ℝ) ^ 64 := by
    change ((W.outputDim ^ 64 : ℕ) : ℝ) = _
    exact Nat.cast_pow _ _
  have h := W.quarticRoot.quarticPermutedDiagonalCorrection_mean_error
    (W.quarticRootExchangeCorrection G) hB (W.quarticRootExchangeCorrection_norm G hG)
    (by positivity : 0 ≤ 1024 * (W.outputDim : ℝ) ^ 130 * ε)
    (W.quarticRootExchangeCorrection_mean_error G hG herr) a b
  apply h.trans_eq
  rw [hdim]
  simp only [← pow_mul, ← pow_add]
  change (W.outputDim : ℝ) ^ 960 * ((W.outputDim : ℝ) ^ 3840 *
    (15 * ((W.outputDim : ℝ) ^ 128 * (1024 * (W.outputDim : ℝ) ^ 130 * ε)))) = _
  calc
    _ = (15 * 1024 : ℝ) * ((W.outputDim : ℝ) ^ 960 * (W.outputDim : ℝ) ^ 3840 *
        (W.outputDim : ℝ) ^ 128 * (W.outputDim : ℝ) ^ 130) * ε := by ac_rfl
    _ = _ := by simp only [← pow_add]; norm_num

theorem exists_quarticRootFifteenCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p), 0 ≤ q →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) = W.eval i x) →
      ∀ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + C) ^ C)
        (W.quarticRootFifteenCorrection G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_quarticRootExchangeCorrection_expansion
  obtain ⟨B, _, hperm⟩ := exists_quartic_root_last_slots_equivalence
  obtain ⟨D, _, hdiagonal⟩ := exists_quartic_permuted_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  let T := 65 * (X + 1) + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hdiagonal W.quarticRoot (W.quarticRootExchangeCorrection G)
    (by positivity : 0 ≤ (p + q + A) ^ A) (by positivity : 0 ≤ (p + B) ^ B)
    (hroot W hq G hG) (hperm W hsymm) a b
  have hcost : (tensorPowerBudget 64 p + (p + q + A) ^ A + (p + B) ^ B + D) ^ D ≤
      (p + q + C) ^ C := by
    have hmono : (p + B) ^ B ≤ (p + q + B) ^ B :=
      pow_le_pow_left₀ (by positivity) (by linarith) B
    have hbound : (65 * (p + q + 1) + (p + q + A) ^ A + (p + q + B) ^ B + D) ^ D ≤
        (p + q + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
    apply le_trans _ hbound
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat]
    linarith
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticRootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.quarticRoot.quarticCyclicDiagonalCorrection N δ (W.quarticRootFifteenCorrection G)

theorem quarticRootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim)
    (b : QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
          star (W.quarticRoot.quarticSymmetricFifteen b (fun k => ((x k).val : ℤ))) -
        W.quarticRootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.quarticRoot.outputDim + 1) *
        (15360 * (W.outputDim : ℝ) ^ 5058 * ε) +
          12 * (δ : ℝ) + 2 / N :=
  W.quarticRoot.quarticCyclicDiagonalCorrection_mean_error δ hδ (W.quarticRootFifteenCorrection G)
    (W.quarticRootFifteenCorrection_mean_error G hε hG herr) a b

theorem exists_quarticRootCyclicCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) = W.eval k x) →
      ∀ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (G π a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + e + C) ^ C)
        (W.quarticRootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_quarticRootFifteenCorrection_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_quarticCyclicDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((65 * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget 64 p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : (65 * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat] at *
    dsimp [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.quarticRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.quarticRootFifteenCorrection G) (hroot W hq hsymm G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p)
  (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticOriginalDiagonalCorrection
    (F : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) →
      (QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) (i : Fin M.outputDim)
    (b : QuarticMiddleIndex W.quarticRoot.outputDim) (c : Fin W.quarticRoot.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ d : Fin 4 → Fin W.quarticRoot.outputDim,
    (M.eval i x * star (W.quarticRoot.quarticHnnnTensor d x)) * F a (quarticGroupedFifteenMerge d b c) x

theorem quarticOriginalDiagonalCorrection_pointwise_error {N : ℕ} [NeZero N]
    (F : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) →
      (QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) (i : Fin M.outputDim)
    (b : QuarticMiddleIndex W.quarticRoot.outputDim) (c : Fin W.quarticRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
        (M.eval i (fun k => ((x k).val : ℤ)) *
          (W.quarticRoot.quarticMiddleTensor b (fun k => ((x k).val : ℤ)) *
            W.quarticRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
      M.quarticOriginalDiagonalCorrection W F a i b c (fun k => ((x k).val : ℤ))‖ ≤
      ∑ d : Fin 4 → Fin W.quarticRoot.outputDim,
        ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
            star (W.quarticRoot.quarticSymmetricFifteen (quarticGroupedFifteenMerge d b c)
              (fun k => ((x k).val : ℤ))) -
          F a (quarticGroupedFifteenMerge d b c) (fun k => ((x k).val : ℤ))‖ := by
  let z : Fin 2 → ℤ := fun k => ((x k).val : ℤ)
  let R := W.quarticRoot
  let D := R.quarticCyclicDiagonalDerivative a x
  have hres := complex_unit_vector_resolution (fun d => R.quarticHnnnTensor d z)
    (R.quarticHnnnTensor_unit z) (M.eval i z)
  have heq : D * (M.eval i z * (R.quarticMiddleTensor b z * R.eval c (fun _ => z 0))) =
      ∑ d : Fin 4 → Fin R.outputDim,
        (M.eval i z * star (R.quarticHnnnTensor d z)) *
          (D * star (R.quarticSymmetricFifteen (quarticGroupedFifteenMerge d b c) z)) := by
    calc
      _ = D * ((∑ d, (M.eval i z * star (R.quarticHnnnTensor d z)) * R.quarticHnnnTensor d z) *
          (R.quarticMiddleTensor b z * R.eval c (fun _ => z 0))) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [R.quarticSymmetricFifteen_grouped_merge]
        ring
  change ‖D * (M.eval i z * (R.quarticMiddleTensor b z * R.eval c (fun _ => z 0))) -
    M.quarticOriginalDiagonalCorrection W F a i b c z‖ ≤ _
  rw [heq, quarticOriginalDiagonalCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [← mul_sub, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right (M.norm_eval i z) (norm_nonneg _)).trans (by
    simpa only [one_mul] using R.quarticHnnnTensor_norm d z)

theorem quarticOriginalDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) →
      (QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
          star (W.quarticRoot.quarticSymmetricFifteen b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) (i : Fin M.outputDim)
    (b : QuarticMiddleIndex W.quarticRoot.outputDim) (c : Fin W.quarticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.quarticRoot.quarticMiddleTensor b (fun k => ((x k).val : ℤ)) *
              W.quarticRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        M.quarticOriginalDiagonalCorrection W F a i b c (fun k => ((x k).val : ℤ))‖) ≤
      (W.quarticRoot.outputDim : ℝ) ^ 4 * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => M.quarticOriginalDiagonalCorrection_pointwise_error W F a i b c x)
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _ : Fin 4 → Fin W.quarticRoot.outputDim, ε :=
      Finset.sum_le_sum (fun d _ => herr a (quarticGroupedFifteenMerge d b c))
    _ = _ := by simp

theorem exists_quarticOriginalDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p)
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p), 0 ≤ q →
      NativeIntegerVectorEquivalence 3 p M.eval (fun k x => W.eval k (quarticInput (x 0) (fun _ => x 1))) →
      ∀ F : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) →
        (QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 q (F a b))) →
      ∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + C) ^ C)
        (M.quarticOriginalDiagonalCorrection W F a i b c)) := by
  obtain ⟨A, _, hcompare⟩ := exists_quartic_original_root_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C B) ^ B + 260 * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q M W hq E F hF a i b c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v] at *
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hterm (d : Fin 4 → Fin W.quarticRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((t + B) ^ B)
        (fun x => (M.eval i x * star (W.quarticRoot.quarticHnnnTensor d x)) *
          F a (quarticGroupedFifteenMerge d b c) x)) :=
    hmul ht ((Classical.choice ((hcompare M W E).expansion i d)).mono hAt)
      ((Classical.choice (hF a (quarticGroupedFifteenMerge d b c))).mono hqt)
  have hcard : (Fintype.card (Fin 4 → Fin W.quarticRoot.outputDim) : ℝ) ≤
      Real.exp (260 * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 64 p) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.quarticRoot.output_bound _
      _ = Real.exp (4 * tensorPowerBudget 64 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 64 p) 4).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        norm_num [tensorPowerBudget]
        dsimp [v]
        linarith
  have hcoeff : (∑ _ : Fin 4 → Fin W.quarticRoot.outputDim, ‖(1 : ℂ)‖) ≤
      Real.exp (260 * (v + 1)) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun d => Classical.choice (hterm d))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ 260 * (v + 1)) hcard hcoeff
  have hcost : (t + B) ^ B + 260 * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 3 ((p + q + C) ^ C)
    (fun x => ∑ d : Fin 4 → Fin W.quarticRoot.outputDim,
      (M.eval i x * star (W.quarticRoot.quarticHnnnTensor d x)) * F a (quarticGroupedFifteenMerge d b c) x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quartic_sampled_exchange_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        W.dim ≤ 16 * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) =
            W.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence 3 q M.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))),
        NativeIntegerVectorEquivalence 3 q (M.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.tensorPower 6).outputDim,
        ∃ V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
          Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ))),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ _R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
          V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
          (fun _ : Fin 4 => (N : ℝ)) r,
        ∃ _D : QuarticMixedRowData M W E (2 * q + 3 * q),
        ∃ G : (Fin 4 → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
          (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
            ((p + e + C) ^ C) (G π a c))) ∧
          (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
          (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
            ‖W.eval a (quarticInput ((x (π 0)).val : ℤ)
                ![((x (π 1)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)]) *
                star (W.eval c (quarticInput ((x (π 1)).val : ℤ)
                  ![((x (π 0)).val : ℤ), ((x (π 2)).val : ℤ), ((x (π 3)).val : ℤ)])) -
              G π a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_quartic_pair_factored_model
  obtain ⟨b, _, hexchange⟩ := exists_quartic_precise_sampled_exchange
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (9 * T + 7 + X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let r := (p + a) ^ a
  let t := (p + e + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [r, t]; gcongr; linarith
  have hsum : t + (9 * t + 7 + (p + e) + b) ^ b ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hrC : r ≤ (p + C) ^ C := by
    have h : r + (9 * r + 7 + p + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, T, r, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right (by positivity)).trans h
  obtain ⟨q, hq, hqr, M, W, hdim, hsymm, E, hdiff, i, j, V, ⟨R⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr (hrt.trans htC)).trans hN) f hf hGowers
  change Fin (W.tensorPower 6).outputDim at i j
  obtain ⟨D⟩ := exists_quartic_mixed_row_data M W E hq
  have hkq : tensorPowerBudget 6 q = 7 * (q + 1) := by norm_num [tensorPowerBudget]
  have hcost : (tensorPowerBudget 6 q + q + r + e + b) ^ b ≤ (p + e + C) ^ C := by
    rw [hkq]
    apply le_trans _ ((le_add_of_nonneg_left ht).trans hsum)
    apply pow_le_pow_left₀ (by positivity)
    have hqr' : q ≤ r := hqr
    linarith
  obtain ⟨G, hG, hcap, herr⟩ := hexchange R hr he ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨q, hq, hqr.trans hrC, M, W, hdim, hsymm, E, hdiff,
    i, j, V, r, hr, hrC, R, D, G,
    fun π a c => ⟨(Classical.choice (hG π a c)).mono hcost⟩, hcap, herr⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quartic_cyclic_comparison_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        W.dim ≤ 16 * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) =
            W.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence 3 q M.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))),
        NativeIntegerVectorEquivalence 3 q (M.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.tensorPower 6).outputDim,
        ∃ V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
          Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ))),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ _R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
          V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
          (fun _ : Fin 4 => (N : ℝ)) r,
        ∃ _D : QuarticMixedRowData M W E (2 * q + 3 * q),
        ∃ K : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) →
            (QuarticNonconstantCorner → Fin W.quarticRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
          (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
            ((p + e + C) ^ C) (K a b))) ∧
          (∀ a b, (𝔼 x : Fin 2 → ZMod N,
            ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
                star (W.quarticRoot.quarticSymmetricFifteen b (fun k => ((x k).val : ℤ))) -
              K a b (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hmodel⟩ := exists_quartic_sampled_exchange_model
  obtain ⟨B, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_quarticRootCyclicCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 5122 * U + 31000 + Polynomial.C A) ^ A
  let S := (U + T + X + 31000 + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + 31000 + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let accuracy := e + 5122 * u + 31000
  let t := (p + accuracy + A) ^ A
  let tmax := (v + 5122 * umax + 31000 + A) ^ A
  let b := e + 31000
  let smax := (umax + tmax + v + 31000 + B) ^ B
  let δ : ℝ≥0 := ⟨Real.exp (-b), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-b) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp b := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + 31000 + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have hbC : b ≤ (p + e + C) ^ C := by dsimp [b, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 5122 * u + 31000 + A) ^ A + p + 31000 +
        (u + (p + 5122 * u + 31000 + A) ^ A + p + 31000 + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 5122 * u + 31000 + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 5122 * u + 31000 + A) ^ A + p + 31000 + B) ^ B := by positivity
    linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, hdiff,
    i, j, V, r, hr, hru, R, D, G, hG, hcap, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + b + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b, v]
    linarith
  have herror := quartic_cyclic_error_bound (Nat.cast_nonneg W.outputDim) hu
    (W.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hsample (π : Fin 4 → Fin 2) (x : Fin 2 → ℤ) :
      quarticSampledInput π x = quarticInput (x (π 0)) ![x (π 1), x (π 2), x (π 3)] := by
    apply congrArg (quarticInput (x (π 0)))
    funext k
    fin_cases k <;> rfl
  have hswap (π : Fin 4 → Fin 2) (x : Fin 2 → ℤ) :
      quarticSampledInput (quarticSwapSample π) x =
        quarticInput (x (π 1)) ![x (π 0), x (π 2), x (π 3)] := by
    rw [hsample]
    rfl
  have hexchange : ∀ π a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (quarticSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval c (quarticSampledInput (quarticSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-accuracy) := by
    intro π a c
    simpa only [hswap, hsample] using herr π a c
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, hdiff,
    i, j, V, r, hr, hru.trans huC, R, D, W.quarticRootCyclicCorrection N δ G, ?_, ?_⟩
  · intro a c
    exact ⟨(Classical.choice (hroot W N δ hδ ht hb hinv hsymm G hG a c)).mono hcost⟩
  · intro a c
    apply (W.quarticRootCyclicCorrection_mean_error δ hδ G (Real.exp_nonneg _) hcap hexchange a c).trans
    have hrootDim : W.quarticRoot.outputDim = W.outputDim ^ 64 := rfl
    simpa only [hrootDim, Nat.cast_pow, hδval, b, accuracy] using herror

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quartic_original_integration :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        W.dim ≤ 16 * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) a).symm j)) =
            W.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence 3 q M.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))),
        NativeIntegerVectorEquivalence 3 q (M.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.tensorPower 6).outputDim,
        ∃ V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
          Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ))),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ _R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
          V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
          (fun _ : Fin 4 => (N : ℝ)) r,
        ∃ _D : QuarticMixedRowData M W E (2 * q + 3 * q),
        ∃ K : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) → Fin M.mixed.outputDim →
            QuarticMiddleIndex W.quarticRoot.outputDim → Fin W.quarticRoot.outputDim → (Fin 2 → ℤ) → ℂ,
          (∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 3
            ((p + e + C) ^ C) (K a i b c))) ∧
          (∀ a i b c, (𝔼 x : Fin 2 → ZMod N,
            ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
                (M.mixed.eval i (fun k => ((x k).val : ℤ)) *
                  (W.quarticRoot.quarticMiddleTensor b (fun k => ((x k).val : ℤ)) *
                    W.quarticRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
              K a i b c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hmodel⟩ := exists_quartic_cyclic_comparison_model
  obtain ⟨B, _, hexpansion⟩ := NativeMultidegreeNilcharacter.exists_quarticOriginalDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 256 * U + Polynomial.C A) ^ A
  let S := (U + T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let accuracy := e + 256 * u
  let t := (p + accuracy + A) ^ A
  let tmax := (v + 256 * umax + A) ^ A
  let smax := (umax + tmax + B) ^ B
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hsum : umax + tmax + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 256 * u + A) ^ A + (u + (p + 256 * u + A) ^ A + B) ^ B ≤
        (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 256 * u + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 256 * u + A) ^ A + B) ^ B := by positivity
    linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, hdiff,
    i, j, V, r, hr, hru, R, D, K, hK, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hd : (W.outputDim : ℝ) ≤ Real.exp u :=
    W.output_bound.trans (Real.exp_le_exp.mpr hqu)
  have hpow : (W.outputDim : ℝ) ^ 256 ≤ Real.exp (256 * u) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hd 256).trans_eq (Real.exp_nat_mul u 256).symm
  have hrootDim : W.quarticRoot.outputDim = W.outputDim ^ 64 := rfl
  have hcube : (W.quarticRoot.outputDim : ℝ) ^ 4 ≤ Real.exp (256 * u) := by
    simpa only [hrootDim, Nat.cast_pow, ← pow_mul, Nat.reduceMul] using hpow
  have herror : (W.quarticRoot.outputDim : ℝ) ^ 4 * Real.exp (-accuracy) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (256 * u) * Real.exp (-accuracy) :=
        mul_le_mul_of_nonneg_right hcube (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [accuracy]; ring
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, hdiff,
    i, j, V, r, hr, hru.trans huC, R, D, M.mixed.quarticOriginalDiagonalCorrection W K, ?_, ?_⟩
  · intro a i b c
    exact ⟨(Classical.choice (hexpansion M.mixed W ht E K hK a i b c)).mono hcost⟩
  · intro a i b c
    exact (M.mixed.quarticOriginalDiagonalCorrection_mean_error W K herr a i b c).trans herror

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem quartic_original_row_correlation_bound {p ε : ℝ} {N : ℕ} [NeZero N]
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p)
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (i : Fin M.outputDim) (row : ZMod N → ZMod N → ℂ)
    (hrow : ∀ h n, ‖row h n‖ ≤ 1)
    (K : (Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) →
      QuarticMiddleIndex W.quarticRoot.outputDim → Fin W.quarticRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quarticRoot.quarticCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.quarticRoot.quarticMiddleTensor b (fun k => ((x k).val : ℤ)) *
              W.quarticRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        K a b c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      row h n * star (M.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ abc : ((Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim) ×
          QuarticMiddleIndex W.quarticRoot.outputDim) × Fin W.quarticRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          row h n *
            (W.quarticRoot.quarticCyclicDiagonalDerivative abc.1.1 ![h, n] *
              W.quarticRoot.quarticMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
                star (K abc.1.1 abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
          (W.quarticRoot.outputDim : ℝ) ^ 13 * ε := by
  let R := W.quarticRoot
  let I := (Fin R.outputDim × Fin R.outputDim) × QuarticMiddleIndex R.outputDim
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : M.evalCyclic N i (correlationInput h n) =
      M.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hunit (h n : ZMod N) : ∑ ab : I,
      ‖R.quarticCyclicDiagonalDerivative ab.1 ![h, n] *
        R.quarticMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)]‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, R.quarticMiddleTensor_unit, mul_one]
    exact R.quarticCyclicDiagonalDerivative_unit _
  have hh := unit_row_correlation_bound row
    (fun h n => M.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun ab : I => fun h n => R.quarticCyclicDiagonalDerivative ab.1 ![h, n] *
      R.quarticMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)])
    (fun c h => R.eval c (fun _ => (h.val : ℤ)))
    (fun ab c h n => K ab.1 ab.2 c ![(h.val : ℤ), (n.val : ℤ)]) hrow hunit
    (fun h => R.unit_eval _) (fun ab h n => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (R.quarticCyclicDiagonalDerivative_norm _ _)
        (norm_nonneg _)).trans (by
          simpa only [one_mul] using R.quarticMiddleTensor_norm _ _))
    (fun c h => R.norm_eval _ _) (ε := ε) (by
      intro ab c
      have he := herr ab.1 ab.2 c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hcard : (Fintype.card (I × Fin R.outputDim) : ℝ) = (R.outputDim : ℝ) ^ 13 := by
    simp only [I, QuarticMiddleIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_pow]
    ring
  simpa only [heval, hcard] using hh

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticPrimitiveFactor {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (i : Fin W.outputDim) (n : ZMod N) : ℂ :=
  f n * W.eval i (fun _ => (n.val : ℤ))

theorem quarticPrimitiveFactor_norm {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i : Fin W.outputDim) (n : ZMod N) :
    ‖W.quarticPrimitiveFactor f i n‖ ≤ 1 := by
  rw [quarticPrimitiveFactor, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)).trans (by
    simpa only [one_mul] using W.norm_eval _ _)

theorem quarticPrimitiveFactor_cross {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (h n : ZMod N) :
    multiplicativeDerivative f h n * W.quarticCyclicDiagonalDerivative a ![h, n] =
      W.quarticPrimitiveFactor f a.1 n * star (W.quarticPrimitiveFactor f a.2 (n + h)) := by
  simp only [multiplicativeDerivative, quarticCyclicDiagonalDerivative, quarticPrimitiveFactor,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_mul]
  rw [add_comm h n]
  ring

end NativeMultidegreeNilcharacter

namespace NativeMixedCorrelation

variable {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation 3 N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticPrimitiveRow (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticMiddleIndex W.outputDim) (h n : ZMod N) : ℂ :=
  (W.quarticPrimitiveFactor f a.1 n * star (W.quarticPrimitiveFactor f a.2 (n + h))) *
    W.quarticMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)] *
      star (M.residualMultiplier h (fun _ => (n.val : ℤ)))

theorem quarticPrimitiveRow_eq (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticMiddleIndex W.outputDim) (h n : ZMod N) :
    M.quarticPrimitiveRow W a b h n = M.normalizedResidualRow h n *
      (W.quarticCyclicDiagonalDerivative a ![h, n] *
        W.quarticMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)]) := by
  rw [quarticPrimitiveRow, M.normalizedResidualRow_factor, ← W.quarticPrimitiveFactor_cross f a h n]
  ring

theorem quarticPrimitiveRow_norm (hf : ∀ n, ‖f n‖ ≤ 1)
    (a : Fin W.outputDim × Fin W.outputDim) (b : QuarticMiddleIndex W.outputDim)
    (h n : ZMod N) : ‖M.quarticPrimitiveRow W a b h n‖ ≤ 1 := by
  rw [M.quarticPrimitiveRow_eq, norm_mul]
  refine (mul_le_mul_of_nonneg_right (M.normalizedResidualRow_norm hf h n)
    (norm_nonneg _)).trans ?_
  rw [one_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (W.quarticCyclicDiagonalDerivative_norm _ _)
    (norm_nonneg _)).trans (by simpa only [one_mul] using W.quarticMiddleTensor_norm _ _)

end NativeMixedCorrelation

theorem exists_quartic_primitive_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
      ∃ a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim,
      ∃ b : QuarticMiddleIndex W.quarticRoot.outputDim,
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) 3 ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (M.quarticPrimitiveRow W.quarticRoot a b)) := by
  obtain ⟨A, _, hintegrate⟩ := exists_quartic_original_integration
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := 65 * (U + 1)
  let E := 4 * U + 13 * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 4 * U + 2 + 13 * R + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := 65 * (u + 1)
  let e := 4 * u + 13 * r + 4
  let t := (p + e + A) ^ A
  let v := 4 * u + 2 + 13 * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, hdiff,
    i, j, Vpair, rpair, hrpair, hrbound, R, D, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  obtain ⟨out, H, hHM, hH, hdense, hcorr⟩ := M.exists_fixed_normalized_residual_coordinate
  let B := W.quarticRoot
  have hroot : tensorPowerBudget 64 q ≤ r := by
    norm_num only [tensorPowerBudget, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hD : (B.outputDim : ℝ) ≤ Real.exp r :=
    B.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hD13 : (B.outputDim : ℝ) ^ 13 ≤ Real.exp (13 * r) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hD 13).trans_eq (Real.exp_nat_mul r 13).symm
  let J := ((Fin B.outputDim × Fin B.outputDim) × QuarticMiddleIndex B.outputDim) × Fin B.outputDim
  let z (abc : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    M.normalizedResidualRow h n *
      (B.quarticCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.quarticMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
          star (K abc.1.1 out abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp (13 * r) := by
    have hc : (Fintype.card J : ℝ) = (B.outputDim : ℝ) ^ 13 := by
      simp only [J, QuarticMiddleIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      ring
    rw [hc]
    exact hD13
  have hmass : Real.exp (-(4 * u)) ≤ 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      M.normalizedResidualRow h n * star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H _ (fun _ => norm_nonneg _)
      (Real.exp_nonneg (-(2 * q))) (by simpa only [ZMod.card] using hdense) hcorr
    have heq : Real.exp (-(2 * q)) * Real.exp (-(2 * q)) = Real.exp (-(4 * q)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by linarith)).trans hh
  have htransfer := M.mixed.quartic_original_row_correlation_bound W out
    M.normalizedResidualRow (M.normalizedResidualRow_norm hf)
    (fun a b c => K a out b c) (fun a b c => herr a out b c)
  change _ ≤ (∑ abc : J, z abc) + (B.outputDim : ℝ) ^ 13 * Real.exp (-e) at htransfer
  let δ := Real.exp (-(4 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (B.outputDim : ℝ) ^ 13 * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp (13 * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hD13 (Real.exp_nonneg _)
      _ = Real.exp (-(4 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(4 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ abc : J, z abc := by linarith
  obtain ⟨abc, habc⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have habc' : Real.exp (-(4 * u + 2 + 13 * r)) ≤ z abc := by
    have heq : δ / Real.exp (13 * r) = Real.exp (-(4 * u + 2 + 13 * r)) := by
      dsimp [δ]; rw [← Real.exp_sub]; congr 1; ring
    rwa [heq] at habc
  let expansion := Classical.choice (hK abc.1.1 out abc.1.2 abc.2)
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion expansion
    (by positivity : 0 ≤ 4 * u + 2 + 13 * r) habc'
  have heq : (fun h n : ZMod N => M.normalizedResidualRow h n *
      (B.quarticCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.quarticMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)])) =
      M.quarticPrimitiveRow B abc.1.1 abc.1.2 := by
    funext h n
    exact (M.quarticPrimitiveRow_eq B abc.1.1 abc.1.2 h n).symm
  refine ⟨q, hq, hqu.trans huC, M, W, abc.1.1, abc.1.2, ?_⟩
  exact ⟨heq ▸ P.mono hvC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

variable {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation 3 N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticResidualRowFactor (b : QuarticMiddleIndex W.outputDim)
    (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  M.residualMultiplier h x * star (W.quarticMiddleTensor b ![(h.val : ℤ), x ()])

theorem quarticResidualRowFactor_norm (b : QuarticMiddleIndex W.outputDim)
    (h : ZMod N) (x : Unit → ℤ) : ‖M.quarticResidualRowFactor W b h x‖ ≤ 1 := by
  rw [quarticResidualRowFactor, norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right (M.residualMultiplier_norm h x)
    (norm_nonneg _)).trans (by simpa only [one_mul] using W.quarticMiddleTensor_norm _ _)

theorem quarticPrimitiveRow_cross_residual (a : Fin W.outputDim × Fin W.outputDim)
    (b : QuarticMiddleIndex W.outputDim) (h n : ZMod N) :
    M.quarticPrimitiveRow W a b h n =
      (W.quarticPrimitiveFactor f a.1 n * star (W.quarticPrimitiveFactor f a.2 (n + h))) *
        star (M.quarticResidualRowFactor W b h (fun _ => (n.val : ℤ))) := by
  simp only [quarticPrimitiveRow, quarticResidualRowFactor, star_mul, star_star]
  ring

theorem exists_quarticResidualRowFactor_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
      (M : NativeMixedCorrelation 3 N m f)
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (b : QuarticMiddleIndex W.outputDim) (h : ZMod N),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 ((m + p + C) ^ C)
        (M.quarticResidualRowFactor W b h)) := by
  obtain ⟨A, _, hmiddle⟩ := NativeMultidegreeNilcharacter.exists_quarticMiddleTensor_row_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro m p N _ f M W b h
  have hm : 0 ≤ m := (Nat.cast_nonneg M.mixed.dim).trans M.mixed.complexity.1.1
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := m + p + (m + p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmt : m ≤ t := by
    have hpow : 0 ≤ (m + p + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ m + p + A by linarith) A).trans
    exact le_add_of_nonneg_left (add_nonneg hm hp)
  obtain ⟨F⟩ := hmul ht ((Classical.choice (M.residualMultiplier_expansion h)).mono hmt)
    ((Classical.choice (hmiddle W h.val b)).conjugate.mono hAt)
  have hcost : (t + B) ^ B ≤ (m + p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (m + p) (add_nonneg hm hp)
  exact ⟨F.mono hcost⟩

end NativeMixedCorrelation

theorem exists_quartic_residual_cross_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
      ∃ a : Fin W.quarticRoot.outputDim × Fin W.quarticRoot.outputDim,
      ∃ b : QuarticMiddleIndex W.quarticRoot.outputDim,
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) 3 ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (fun h n =>
            (W.quarticRoot.quarticPrimitiveFactor f a.1 n *
              star (W.quarticRoot.quarticPrimitiveFactor f a.2 (n + h))) *
                star (M.quarticResidualRowFactor W.quarticRoot b h (fun _ => (n.val : ℤ))))) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 ((p + C) ^ C)
          (M.quarticResidualRowFactor W.quarticRoot b h))) ∧
        (∀ h x, ‖M.quarticResidualRowFactor W.quarticRoot b h x‖ ≤ 1) := by
  obtain ⟨A, _, hrows⟩ := exists_quartic_primitive_rows
  obtain ⟨B, _, hfactor⟩ := NativeMixedCorrelation.exists_quarticResidualRowFactor_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (66 * (U + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (66 * (u + 1) + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hcost : (q + tensorPowerBudget 64 q + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ ((le_add_of_nonneg_left hu).trans hsum)
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat]
    linarith
  have heq : M.quarticPrimitiveRow W.quarticRoot a b =
      (fun h n =>
        (W.quarticRoot.quarticPrimitiveFactor f a.1 n *
          star (W.quarticRoot.quarticPrimitiveFactor f a.2 (n + h))) *
            star (M.quarticResidualRowFactor W.quarticRoot b h (fun _ => (n.val : ℤ)))) := by
    funext h n
    exact M.quarticPrimitiveRow_cross_residual W.quarticRoot a b h n
  refine ⟨q, hq, hqu.trans huC, M, W, a, b, ⟨heq ▸ V.mono huC⟩, ?_, ?_⟩
  · intro h
    exact ⟨(Classical.choice (hfactor M W.quarticRoot b h)).mono hcost⟩
  · intro h x
    exact M.quarticResidualRowFactor_norm W.quarticRoot b h x

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_quartic_primitive_gowers_four :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        ∃ i : Fin W.outputDim,
          Real.exp (-((p + C) ^ C)) ≤ gowersNorm 4 (W.quarticPrimitiveFactor f i) := by
  obtain ⟨A, _, hrows⟩ := exists_quartic_residual_cross_rows
  obtain ⟨B, _, hcross⟩ := RationalFilteredNilmanifold.exists_gowers_four_of_cubic_residual_cross_rows
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + 65 * (U + 1) + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + 65 * (u + 1) + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩, hR, hRnorm⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hc := hcross V.model V.test hu V.complexity
    ((Real.exp_le_exp.mpr hvC).trans hN)
    (W.quarticRoot.quarticPrimitiveFactor f a.1) (W.quarticRoot.quarticPrimitiveFactor f a.2)
    (M.quarticResidualRowFactor W.quarticRoot b)
    (W.quarticRoot.quarticPrimitiveFactor_norm f hf a.1)
    (W.quarticRoot.quarticPrimitiveFactor_norm f hf a.2)
    (fun h n => hRnorm h (fun _ => (n.val : ℤ))) hR V.correlation
  have hroot : 0 ≤ tensorPowerBudget 64 q := by unfold tensorPowerBudget; positivity
  have hrootC : tensorPowerBudget 64 q ≤ (p + C) ^ C := by
    norm_num only [tensorPowerBudget, Nat.cast_ofNat]
    linarith
  exact ⟨tensorPowerBudget 64 q, hroot, hrootC, W.quarticRoot, a.2,
    (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hc⟩

end Erdos3

end

end OAI
