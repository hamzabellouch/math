import OAI.Analysis.CoulombTransport.CoulombCalculus

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniform lower Hessian bound away from a Coulomb collision. -/
theorem pairHessian_quadratic_lower_of_two_thirds {a : E}
    (ha : (2 : ℝ) / 3 ≤ ‖a‖) (u : E) :
    -(27 / 8 : ℝ) * ‖u‖ ^ 2 ≤ ⟪u, pairHessian a u⟫ := by
  have hn : 0 < ‖a‖ := lt_of_lt_of_le (by norm_num) ha
  have hp : ((2 : ℝ) / 3) ^ 3 ≤ ‖a‖ ^ 3 :=
    pow_le_pow_left₀ (by norm_num) ha 3
  have hi : (‖a‖ ^ 3)⁻¹ ≤ (27 / 8 : ℝ) := by
    have hh := (inv_le_inv₀ (pow_pos hn 3) (by norm_num : 0 < ((2 : ℝ) / 3) ^ 3)).2 hp
    norm_num at hh ⊢
    exact hh
  have hm := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖u‖)
  have hl := pairHessian_quadratic_lower a u
  rw [real_inner_comm] at hl
  linarith

/-- The explicit K=20 regularization dominates every negative Coulomb Hessian
contribution on a domain where all three pair distances are at least 2/3. -/
theorem regularized_hessian_coercive_of_separated
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖) (u v : E) :
    (79 / 8 : ℝ) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
      20 * (‖u‖ ^ 2 + ‖v‖ ^ 2) +
        ⟪u, pairHessian a u⟫ +
        ⟪u - v, pairHessian b (u - v)⟫ +
        ⟪v, pairHessian c v⟫ := by
  have h₁ := pairHessian_quadratic_lower_of_two_thirds ha u
  have h₂ := pairHessian_quadratic_lower_of_two_thirds hb (u - v)
  have h₃ := pairHessian_quadratic_lower_of_two_thirds hc v
  have hnorm : ‖u - v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (u - v)) (norm_sub_le u v) 2
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

/-- Strict positivity for every nonzero state direction. -/
theorem regularized_hessian_pos_of_separated
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖)
    {u v : E} (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < 20 * (‖u‖ ^ 2 + ‖v‖ ^ 2) +
        ⟪u, pairHessian a u⟫ +
        ⟪u - v, pairHessian b (u - v)⟫ +
        ⟪v, pairHessian c v⟫ := by
  have hsum : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rcases huv with hu | hv
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hu)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  exact lt_of_lt_of_le (mul_pos (by norm_num) hsum)
    (regularized_hessian_coercive_of_separated ha hb hc u v)

/-- The regularized state-Jacobian, written in component form suitable for the
parameter/state stationarity equation. -/
def regularizedStateHessian (a b c : E) : (E × E) →L[ℝ] E × E :=
  (((pairHessian a).comp (ContinuousLinearMap.fst ℝ E E) +
      (pairHessian b).comp
        (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)) +
      (20 : ℝ) • ContinuousLinearMap.fst ℝ E E).prod
    ((-((pairHessian b).comp
        (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)) +
      (pairHessian c).comp (ContinuousLinearMap.snd ℝ E E)) +
      (20 : ℝ) • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem regularizedStateHessian_apply (a b c u v : E) :
    regularizedStateHessian a b c (u, v) =
      (pairHessian a u + pairHessian b (u - v) + (20 : ℝ) • u,
        -(pairHessian b (u - v)) + pairHessian c v + (20 : ℝ) • v) := rfl

/-- Expansion of the product-state quadratic form. -/
theorem regularizedStateHessian_quadratic (a b c : E) (q : E × E) :
    ⟪q.1, (regularizedStateHessian a b c q).1⟫ +
        ⟪q.2, (regularizedStateHessian a b c q).2⟫ =
      20 * (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) +
        ⟪q.1, pairHessian a q.1⟫ +
        ⟪q.1 - q.2, pairHessian b (q.1 - q.2)⟫ +
        ⟪q.2, pairHessian c q.2⟫ := by
  rcases q with ⟨u, v⟩
  simp only [regularizedStateHessian_apply, inner_add_right, inner_neg_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, inner_sub_left]
  ring

/-- Quantitative coercivity of the state-Jacobian in the actual max product norm. -/
theorem regularizedStateHessian_coercive
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖) (q : E × E) :
    (79 / 8 : ℝ) * ‖q‖ ^ 2 ≤
      ⟪q.1, (regularizedStateHessian a b c q).1⟫ +
        ⟪q.2, (regularizedStateHessian a b c q).2⟫ := by
  rw [regularizedStateHessian_quadratic]
  have hnorm : ‖q‖ ^ 2 ≤ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖q.1‖ ‖q.2‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (sq_nonneg _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans
    (regularized_hessian_coercive_of_separated ha hb hc q.1 q.2)

/-- Strict positivity in every nonzero direction. -/
theorem regularizedStateHessian_pos
    {a b c : E} (ha : (2 : ℝ) / 3 ≤ ‖a‖)
    (hb : (2 : ℝ) / 3 ≤ ‖b‖) (hc : (2 : ℝ) / 3 ≤ ‖c‖)
    {q : E × E} (hq : q ≠ 0) :
    0 < ⟪q.1, (regularizedStateHessian a b c q).1⟫ +
        ⟪q.2, (regularizedStateHessian a b c q).2⟫ :=
  lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hq)))
    (regularizedStateHessian_coercive ha hb hc q)

/-- The explicit Jacobian of the regularized Coulomb stationarity equation.
The constant vector in the second component accommodates the chosen outer
potential and has no effect on the Hessian. -/
theorem hasFDerivAt_regularizedStateGradient (y k : E) {s : E × E}
    (hxy : s.1 - y ≠ 0) (hxz : s.1 - s.2 ≠ 0) (hzy : s.2 - y ≠ 0) :
    HasFDerivAt
      (fun p : E × E =>
        (pairGradient (p.1 - y) + pairGradient (p.1 - p.2) + (20 : ℝ) • p.1,
          -pairGradient (p.1 - p.2) + pairGradient (p.2 - y) +
            (20 : ℝ) • p.2 + k))
      (regularizedStateHessian (s.1 - y) (s.1 - s.2) (s.2 - y)) s := by
  have hx : HasFDerivAt (fun p : E × E => p.1) (ContinuousLinearMap.fst ℝ E E) s :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hz : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) s :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have h₁ := (hasFDerivAt_pairGradient hxy).comp s (hx.sub_const y)
  have h₂ := (hasFDerivAt_pairGradient hxz).comp s (hx.sub hz)
  have h₃ := (hasFDerivAt_pairGradient hzy).comp s (hz.sub_const y)
  exact ((h₁.add h₂).add (hx.const_smul (20 : ℝ))).prodMk
    (((h₂.neg.add h₃).add (hz.const_smul (20 : ℝ))).add_const k)

end Problem356.CoulombCalculus

end

end OAI
