import OAI.Combinatorics.Progressions.Fourier.NativeCharacterCrossFamily

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_residual_row_differences_degree_three :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L 3 d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (F : ZMod N → ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        (F h n * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
      ∃ J : ZMod N → ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + C) ^ C) (K k))) ∧
        (∀ k h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C) (J k h))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
            star (J k h (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model 3
  obtain ⟨B, _, hrows⟩ := exists_unit_row_family_with_differences 1 (by omega)
  obtain ⟨D₀, _, hcyclic⟩ :=
    UnitVerticalObservable.exists_cyclic_second_difference_models_degree 2 (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let T₀ := X + Q + 4
  let V₀ := (T₀ + Polynomial.C B) ^ B
  let E₁ := 2 * V₀ + 4
  let A₀ := (Q + E₁ + Polynomial.C D₀) ^ D₀
  let E₂ := E₁ + 2 * A₀
  let B₀ := (T₀ + E₂ + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + B₀ + 2 * V₀ + E₂ + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN F R hF hR hRE hcorr
  classical
  let q := (p + A) ^ A
  let t := p + q + 4
  let v := (t + B) ^ B
  let e₁ := 2 * v + 4
  let a := (q + e₁ + D₀) ^ D₀
  let e₂ := e₁ + 2 * a
  let b := (t + e₂ + B) ^ B
  let z := 2 * v + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp [e₂]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hsum : a + b + 2 * v + e₂ + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, T₀, V₀, E₁, A₀, E₂, B₀, q, t, v, e₁, a, e₂, b,
      Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hzC : z ≤ (p + C) ^ C := by dsimp [z]; linarith
  have hN₁ : Real.exp (e₁ + 16) ≤ (N : ℝ) := by
    apply (Real.exp_le_exp.mpr ?_).trans hN
    dsimp [e₂] at hsum
    linarith
  have hN₂ : Real.exp (e₂ + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n => F h n * star (R h (fun _ => (n.val : ℤ)))) (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)) hcorr
  let u (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hu (h n : ZMod N) : ‖u h n‖ ≤ 1 := (V.test T.orbit 0).norm_eval_le _
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hrowcorr : Real.exp (-t) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      (F h n * star (u h n)) * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans
    apply hVcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨G, hG, _, hGcorr, hGdiff⟩ := hrows ht
    (fun h n => F h n * star (u h n)) R (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hu h n)) hR
    (fun h => ⟨(Classical.choice (hRE h)).mono hpt⟩) hrowcorr
  have hbase : Real.exp (-v) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (u h n * G h (fun _ => (n.val : ℤ)))‖) := by
    simpa only [star_mul, mul_comm, mul_left_comm, mul_assoc] using hGcorr
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 a K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e₁) :=
    hcyclic D V T.orbit hq hD hcard he₁ hN₁ 0 0 k
  choose K hK herrK using hmodels
  have hrowmodels (k h : ZMod N) : ∃ J : (Unit → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 b J) ∧
      (𝔼 n : ZMod N,
        ‖G h (fun _ => (n.val : ℤ)) * star (G h (fun _ => ((n + k).val : ℤ))) -
          J (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e₂) :=
    hGdiff he₂ hN₂ h k
  choose J hJ herrJ using hrowmodels
  have hd := mean_row_correlation_sq_le_product_derivatives F u
    (fun h n => G h (fun _ => (n.val : ℤ)))
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)])
    (fun k h n => J k h (fun _ => (n.val : ℤ)))
    (B := Real.exp (2 * a)) (ε := Real.exp (-e₁)) (δ := Real.exp (-e₂))
    hF (fun h n => hG h _) (Real.exp_nonneg _) (by
      intro k h n
      exact (Classical.choice (hK k)).norm_eval_le _) (by
      intro k h
      simpa only [u, multiplicativeDerivative, cyclicSecondDifference] using herrK k h.val) (by
      intro k h
      simpa only [multiplicativeDerivative] using herrJ k h)
  have hlarge : Real.exp (-(2 * v)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
        star (J k h (fun _ => (n.val : ℤ)))‖) +
          (Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂)) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-v)) hbase 2).trans hd
    have hexp : Real.exp (-v) ^ 2 = Real.exp (-(2 * v)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [hexp, star_mul, mul_comm, mul_left_comm, mul_assoc] using hsquare
  have herror : Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂) ≤ Real.exp (-z) := by
    have hmul : Real.exp (2 * a) * Real.exp (-e₂) = Real.exp (-e₁) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [e₂]
      ring
    rw [hmul]
    calc
      _ = 2 * Real.exp (-e₁) := by ring
      _ ≤ Real.exp 2 * Real.exp (-e₁) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e₁, z]; ring
  have htwo : 2 * Real.exp (-z) ≤ Real.exp (-(2 * v)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-z) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [z]; ring
  refine ⟨K, J, fun k => ⟨(Classical.choice (hK k)).mono haC⟩,
    fun k h => ⟨(Classical.choice (hJ k h)).mono hbC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg hzC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_gowers_four_of_mixed_differences :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ},
      0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (f g : ZMod N → ℂ) (K : ZMod N → (Fin 2 → ℤ) → ℂ)
        (L : ZMod N → ZMod N → (Unit → ℤ) → ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 p (K k))) →
      (∀ k h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 p (L k h))) →
      Real.exp (-p) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
        (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
          star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
          star (L k h (fun _ => (n.val : ℤ)))‖) →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm 4 g := by
  obtain ⟨A, _, hlinear⟩ := exists_characters_of_stepOne_rows
  obtain ⟨D, _, hdetect⟩ := exists_native_character_cross_row_detection 2 (by norm_num)
  obtain ⟨B, _, hfamily⟩ := exists_gowers_of_native_character_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let W := 3 * X + 2
  let V := (W + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (V + (V + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f g K L hf hg hK hL hcorr
  classical
  let w := 3 * p + 2
  let v := (w + A) ^ A + p + 2
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hpw : p ≤ w := by dsimp [w]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpv : p ≤ v := by
    have hpow : 0 ≤ (w + A) ^ A := by positivity
    dsimp [v]
    linarith
  have hscore : (w + A) ^ A ≤ v := by dsimp [v]; linarith
  have hcost : v + (v + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, W, V, w, v, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (v + B) ^ B ≤ (p + C) ^ C := by linarith
  let F : (ZMod N × ZMod N) → ZMod N → ℂ := fun kh n =>
    (multiplicativeDerivative f kh.1 n * star (multiplicativeDerivative g kh.1 (n + kh.2))) *
      star (K kh.1 ![(kh.2.val : ℤ), (n.val : ℤ)])
  let R : (ZMod N × ZMod N) → (Unit → ℤ) → ℂ := fun kh x =>
    (Real.exp (-(2 * p)) : ℂ) * L kh.1 kh.2 x
  have hF (kh : ZMod N × ZMod N) (n : ZMod N) : ‖F kh n‖ ≤ Real.exp w := by
    have hcross : ‖multiplicativeDerivative f kh.1 n *
        star (multiplicativeDerivative g kh.1 (n + kh.2))‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (multiplicativeDerivative_norm_le_one f hf kh.1 n)).trans
          (multiplicativeDerivative_norm_le_one g hg kh.1 (n + kh.2))
    change ‖(multiplicativeDerivative f kh.1 n *
      star (multiplicativeDerivative g kh.1 (n + kh.2))) *
      star (K kh.1 ![(kh.2.val : ℤ), (n.val : ℤ)])‖ ≤ Real.exp w
    rw [norm_mul, norm_star]
    exact ((mul_le_of_le_one_left (norm_nonneg _) hcross).trans
      ((Classical.choice (hK kh.1)).norm_eval_le _)).trans
      (Real.exp_le_exp.mpr (by dsimp [w]; linarith))
  have hR (kh : ZMod N × ZMod N) (n : ZMod N) :
      ‖R kh (fun _ => (n.val : ℤ))‖ ≤ 1 := by
    simp only [R, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left ((Classical.choice (hL kh.1 kh.2)).norm_eval_le _)
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hRE (kh : ZMod N × ZMod N) :
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 w (R kh)) := by
    apply Nonempty.intro
    apply NativeIntegerExpansion.mono _ hpw
    apply (Classical.choice (hL kh.1 kh.2)).scaleNormLeOne
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr (by linarith : -(2 * p) ≤ 0))
  have hscale (kh : ZMod N × ZMod N) :
      ‖𝔼 n : ZMod N, F kh n * star (R kh (fun _ => (n.val : ℤ)))‖ =
        Real.exp (-(2 * p)) *
          ‖𝔼 n : ZMod N, F kh n * star (L kh.1 kh.2 (fun _ => (n.val : ℤ)))‖ := by
    have heq : (𝔼 n : ZMod N, F kh n * star (R kh (fun _ => (n.val : ℤ)))) =
        (Real.exp (-(2 * p)) : ℂ) *
          (𝔼 n : ZMod N, F kh n * star (L kh.1 kh.2 (fun _ => (n.val : ℤ)))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      change F kh n * star ((Real.exp (-(2 * p)) : ℂ) *
        L kh.1 kh.2 (fun _ => (n.val : ℤ))) = _
      rw [star_mul]
      rw [show star ((Real.exp (-(2 * p))) : ℂ) = (Real.exp (-(2 * p)) : ℂ) from
        Complex.conj_ofReal _]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hscaled : Real.exp (-w) ≤
      𝔼 kh, ‖𝔼 n : ZMod N, F kh n * star (R kh (fun _ => (n.val : ℤ)))‖ := by
    simp only [hscale, ← Finset.mul_expect]
    rw [expect_prod_split]
    apply (Real.exp_le_exp.mpr (show -w ≤ -(3 * p) by dsimp [w]; linarith)).trans
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨χ, hχ⟩ := hlinear hw F R hF hR hRE hscaled
  have hchars : Real.exp (-v) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      characterCrossRow (multiplicativeDerivative f k) (multiplicativeDerivative g k)
        (fun h => χ (k, h)) h n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hscore)).trans
    apply hχ.trans_eq
    rw [expect_prod_split]
    apply Finset.expect_congr rfl
    intro k _
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    dsimp [F, characterCrossRow]
    ring
  have hmean := hfamily hv ((Real.exp_le_exp.mpr hresult).trans hN)
    (multiplicativeDerivative f) (multiplicativeDerivative g) (fun k h => χ (k, h)) K
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    (fun k => ⟨(Classical.choice (hK k)).mono hpv⟩) hchars
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (exp_le_gowers_of_mean_derivative 2 g (by positivity : 0 ≤ (v + B) ^ B) hmean)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_gowers_four_of_cubic_residual_cross_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L 3 d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 2 p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm 4 g := by
  obtain ⟨A, _, hdifference⟩ := exists_residual_row_differences_degree_three
  obtain ⟨B, _, hgowers⟩ := exists_gowers_four_of_mixed_differences
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, J, hK, hJ, hdiff⟩ := hdifference D T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (fun h n => f n * star (g (n + h))) R
    (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))) hR hRE hcorr
  have hderiv (h k n : ZMod N) :
      multiplicativeDerivative (fun n => f n * star (g (n + h))) k n =
        multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h)) := by
    simp only [multiplicativeDerivative, star_mul, star_star]
    rw [add_right_comm n k h]
    ring
  have hclean : Real.exp (-u) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
        star (J k h (fun _ => (n.val : ℤ)))‖) := by
    simpa only [hderiv] using hdiff
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (hgowers hu ((Real.exp_le_exp.mpr hvC).trans hN) f g K J hf hg hK hJ hclean)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
