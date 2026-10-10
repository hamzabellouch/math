import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEGrowthExpression

namespace OAI

/-! # Coarse exponential bounds for every exterior ODE derivative

Constants depend on the derivative order and the actual solution.  They do
not involve a comparison or truncation polynomial.  This is the growth
input needed to recover differentiated asymptotics by interpolation.
-/

open Set Filter Topology

namespace DefocusingNLS

namespace RadialODEExpr

theorem eval_exponential_bound (a : RadialODEExpr) (f g : ℝ → ℂ) (M U : ℝ)
    (hM : 0 ≤ M) (hf : ∀ t, U ≤ t → ‖f t‖ ≤ M) (hg : ∀ t, U ≤ t → ‖g t‖ ≤ M) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ t, U ≤ t → 0 ≤ t →
      ‖eval f g t a‖ ≤ B * Real.exp (C * t) := by
  induction a with
  | constant c =>
      refine ⟨0, ‖c‖, le_rfl, norm_nonneg _, ?_⟩
      intro t ht ht0
      simp only [eval, zero_mul, Real.exp_zero, mul_one, le_refl]
  | exponential =>
      refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
      intro t ht ht0
      simp only [eval, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), one_mul, le_refl]
  | position =>
      refine ⟨0, M, le_rfl, hM, ?_⟩
      intro t ht ht0
      simpa only [eval, zero_mul, Real.exp_zero, mul_one] using hf t ht
  | velocity =>
      refine ⟨0, M, le_rfl, hM, ?_⟩
      intro t ht ht0
      simpa only [eval, zero_mul, Real.exp_zero, mul_one] using hg t ht
  | add a b ha hb =>
      obtain ⟨Ca, Ba, hCa, hBa, hba⟩ := ha
      obtain ⟨Cb, Bb, hCb, hBb, hbb⟩ := hb
      refine ⟨Ca + Cb, Ba + Bb, add_nonneg hCa hCb, add_nonneg hBa hBb, ?_⟩
      intro t ht ht0
      have hea : Real.exp (Ca * t) ≤ Real.exp ((Ca + Cb) * t) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have heb : Real.exp (Cb * t) ≤ Real.exp ((Ca + Cb) * t) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc
        ‖eval f g t (add a b)‖ ≤ ‖eval f g t a‖ + ‖eval f g t b‖ := norm_add_le _ _
        _ ≤ Ba * Real.exp (Ca * t) + Bb * Real.exp (Cb * t) :=
          add_le_add (hba t ht ht0) (hbb t ht ht0)
        _ ≤ Ba * Real.exp ((Ca + Cb) * t) + Bb * Real.exp ((Ca + Cb) * t) :=
          add_le_add (mul_le_mul_of_nonneg_left hea hBa) (mul_le_mul_of_nonneg_left heb hBb)
        _ = _ := by ring
  | mul a b ha hb =>
      obtain ⟨Ca, Ba, hCa, hBa, hba⟩ := ha
      obtain ⟨Cb, Bb, hCb, hBb, hbb⟩ := hb
      refine ⟨Ca + Cb, Ba * Bb, add_nonneg hCa hCb, mul_nonneg hBa hBb, ?_⟩
      intro t ht ht0
      calc
        ‖eval f g t (mul a b)‖ = ‖eval f g t a‖ * ‖eval f g t b‖ := norm_mul _ _
        _ ≤ (Ba * Real.exp (Ca * t)) * (Bb * Real.exp (Cb * t)) :=
          mul_le_mul (hba t ht ht0) (hbb t ht ht0) (norm_nonneg _)
            (mul_nonneg hBa (Real.exp_pos _).le)
        _ = (Ba * Bb) * (Real.exp (Ca * t) * Real.exp (Cb * t)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
  | conjugate a ha =>
      obtain ⟨C, B, hC, hB, hb⟩ := ha
      refine ⟨C, B, hC, hB, ?_⟩
      intro t ht ht0
      simpa only [eval, norm_star] using hb t ht ht0

end RadialODEExpr

theorem radialExterior_position_derivatives_exponential_bound
    (ν : ℂ) (n : ℕ) (Z : ℝ → ℂ × ℂ) (L U M : ℝ) (hM : 0 ≤ M)
    (hZ : ∀ t, L < t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t)
    (hb : ∀ t, U ≤ t → ‖Z t‖ ≤ M) (k : ℕ) :
    ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ L < T ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k (fun s => (Z s).1) t‖ ≤ B * Real.exp (C * t) := by
  let f : ℝ → ℂ := fun t => (Z t).1
  let g : ℝ → ℂ := fun t => (Z t).2
  have hf : ∀ t, L < t → HasDerivAt f (g t) t := by
    intro t ht
    exact (hZ t ht).fst
  have hg : ∀ t, L < t →
      HasDerivAt g (RadialODEExpr.eval f g t (RadialODEExpr.acceleration ν n)) t := by
    intro t ht
    have hh := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hZ t ht)
    change HasDerivAt g
      (-(2 * ν + 10 + Complex.I * (Real.exp (2 * t) / 2 : ℝ)) * g t -
        ν * (ν + 10) * f t + oddPowerNonlinearity n (f t)) t at hh
    simpa only [RadialODEExpr.eval_acceleration] using hh
  obtain ⟨C, B, hC, hB, hbound⟩ := RadialODEExpr.eval_exponential_bound
    ((RadialODEExpr.differentiate ν n)^[k] RadialODEExpr.position) f g M U hM
    (fun t ht => (norm_fst_le (Z t)).trans (hb t ht))
    (fun t ht => (norm_snd_le (Z t)).trans (hb t ht))
  let T := max U (max 0 (L + 1))
  have hLT : L < T := lt_of_lt_of_le (by linarith : L < L + 1)
    ((le_max_right 0 _).trans (le_max_right U _))
  refine ⟨C, B, T, hC, hB, hLT, ?_⟩
  intro t ht
  rw [RadialODEExpr.iteratedDeriv_position ν n f g L hf hg k t (hLT.trans_le ht)]
  exact hbound t ((le_max_left U _).trans ht)
    (((le_max_left 0 _).trans (le_max_right U _)).trans ht)

theorem HasRadialOutgoingExpansion.derivatives_exponential_bound
    {ν m : ℂ} {n : ℕ} {Z : ℝ → ℂ × ℂ} (h : HasRadialOutgoingExpansion ν n m Z)
    (L : ℝ) (hZ : ∀ t, L < t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t)
    (k : ℕ) :
    ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ L < T ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k (fun s => (Z s).1) t‖ ≤ B * Real.exp (C * t) := by
  have he : ∀ᶠ t in atTop, ‖Z t‖ < ‖(m, (0 : ℂ))‖ + 1 :=
    h.tendsto.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨U, hU⟩ := eventually_atTop.mp he
  exact radialExterior_position_derivatives_exponential_bound ν n Z L U
    (‖(m, (0 : ℂ))‖ + 1) (by positivity) hZ (fun t ht => (hU t ht).le) k

end DefocusingNLS

end OAI
