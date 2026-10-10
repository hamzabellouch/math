import OAI.MathematicalPhysics.AlternatingFlow.Model

namespace OAI

section QuantitativeDevelopment

open scoped BigOperators ContDiff

namespace AlternatingNS
namespace Quantitative

noncomputable def rhoTerm (m : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ m * expNegInvGlue x

lemma rhoTerm_smooth (m : ℕ) : ContDiff ℝ ∞ (rhoTerm m) := by
  change ContDiff ℝ ∞ (fun x => x⁻¹ ^ m * expNegInvGlue x)
  simpa only [Polynomial.eval_X_pow] using
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X ^ m : Polynomial ℝ))

lemma rhoTerm_deriv (m : ℕ) :
    deriv (rhoTerm m) = fun x => rhoTerm (m + 2) x - m * rhoTerm (m + 1) x := by
  funext x
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.X ^ m : Polynomial ℝ) x).deriv
  simp only [Polynomial.eval_X_pow] at h
  change deriv (rhoTerm m) x = _ at h
  rw [h]
  simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X_pow, rhoTerm]
  cases m with
  | zero => norm_num
  | succ m => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]; ring

lemma exp_monomial_bound (y : ℝ) (hy : 0 ≤ y) (m : ℕ) :
    y ^ m * Real.exp (-y) ≤ m.factorial := by
  have h := Real.pow_div_factorial_le_exp y hy m
  have hp : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h' := (div_le_iff₀ hp).mp h
  calc
    _ ≤ (Real.exp y * m.factorial) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; simp

lemma rhoTerm_bound (m : ℕ) (x : ℝ) : |rhoTerm m x| ≤ m.factorial := by
  by_cases hx : x ≤ 0
  · simp [rhoTerm, expNegInvGlue.zero_of_nonpos hx]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [rhoTerm, expNegInvGlue, ite_eq_right hx,
      abs_of_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hx').le _) (Real.exp_pos _).le)]
    exact exp_monomial_bound x⁻¹ (inv_pos.mpr hx').le m

lemma rhoTerm_derivative_bound (r m : ℕ) (x : ℝ) :
    |iteratedDeriv r (rhoTerm m) x| ≤
      ((m + 2 * r).factorial : ℝ) * (m + 2 * r + 1 : ℕ) ^ r := by
  induction r generalizing m with
  | zero => simpa using rhoTerm_bound m x
  | succ r ih =>
    rw [iteratedDeriv_succ', rhoTerm_deriv]
    have hs (j : ℕ) : ContDiffAt ℝ (r : ℕ∞ω) (rhoTerm j) x :=
      ((rhoTerm_smooth j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    change |iteratedDeriv r (rhoTerm (m + 2) - fun x => (m : ℝ) * rhoTerm (m + 1) x) x| ≤ _
    rw [iteratedDeriv_sub (hs _) (contDiffAt_const.mul (hs _)), iteratedDeriv_const_mul _ (hs _)]
    have ht : m + 2 + 2 * r = m + 2 * (r + 1) := by omega
    have hf : ((m + 1 + 2 * r).factorial : ℝ) ≤ (m + 2 * (r + 1)).factorial := by
      exact_mod_cast Nat.factorial_le (by omega : m + 1 + 2 * r ≤ m + 2 * (r + 1))
    have hp : ((m + 1 + 2 * r + 1 : ℕ) : ℝ) ^ r ≤ (m + 2 * (r + 1) + 1 : ℕ) ^ r := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (by omega : m + 1 + 2 * r + 1 ≤ m + 2 * (r + 1) + 1)
    have hsmall := (ih (m + 1)).trans (mul_le_mul hf hp (by positivity) (by positivity))
    have hbig := ih (m + 2)
    rw [ht] at hbig
    calc
      _ ≤ |iteratedDeriv r (rhoTerm (m + 2)) x| + (m : ℝ) * |iteratedDeriv r (rhoTerm (m + 1)) x| := by
        simpa only [Real.norm_eq_abs, abs_mul, Nat.abs_cast] using
          norm_sub_le (iteratedDeriv r (rhoTerm (m + 2)) x) ((m : ℝ) * iteratedDeriv r (rhoTerm (m + 1)) x)
      _ ≤ ((m + 2 * (r + 1)).factorial : ℝ) * (m + 2 * (r + 1) + 1 : ℕ) ^ r +
          m * (((m + 2 * (r + 1)).factorial : ℝ) * (m + 2 * (r + 1) + 1 : ℕ) ^ r) :=
        add_le_add hbig (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _))
      _ ≤ _ := by
        rw [pow_succ]
        have hm : (m : ℝ) + 1 ≤ (m + 2 * (r + 1) + 1 : ℕ) := by
          push_cast; nlinarith
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m + 2 * (r + 1)).factorial by positivity)
          (show (0 : ℝ) ≤ (m + 2 * (r + 1) + 1 : ℕ) ^ r by positivity)]

lemma rho_derivative_bound (r : ℕ) (x : ℝ) :
    |iteratedDeriv r expNegInvGlue x| ≤ ((2 * r).factorial : ℝ) * (2 * r + 1 : ℕ) ^ r := by
  have he : rhoTerm 0 = expNegInvGlue := by funext x; simp [rhoTerm]
  simpa only [he, zero_add] using rhoTerm_derivative_bound r 0 x

def rhoBound (r : ℕ) : ℕ := (2 * r).factorial * (2 * r + 1) ^ r

lemma rho_jet_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r expNegInvGlue x‖ ≤ rhoBound r := by
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    rhoBound, Nat.cast_mul, Nat.cast_pow] using rho_derivative_bound r x

lemma transition_denom_lower (x : ℝ) :
    (1 / 9 : ℝ) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have he : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg]
    apply (le_inv_comm₀ (by norm_num) (Real.exp_pos _)).mpr
    have h : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
      simp
    rw [h]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hhalf : (1 / 9 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    norm_num [expNegInvGlue] at *
    exact he
  by_cases hx : (1 / 2 : ℝ) ≤ x
  · exact le_trans (hhalf.trans (expNegInvGlue.monotone hx))
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
  · exact le_trans (hhalf.trans (expNegInvGlue.monotone (by linarith : 1 / 2 ≤ 1 - x)))
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _))

lemma inverse_jet_bound (q r : ℕ) {x : ℝ} (hx : 0 < x) (hq : x⁻¹ ≤ q) :
    ‖iteratedFDeriv ℝ r (fun x : ℝ => x⁻¹) x‖ ≤ (r.factorial * q ^ (r + 1) : ℕ) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hexp : (-1 - (r : ℤ)) = -((r + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← inv_pow, norm_mul, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    Nat.abs_cast, Nat.cast_mul, Nat.cast_pow,
    abs_of_nonneg (pow_nonneg (inv_pos.mpr hx).le _)]
  gcongr

def reciprocalBound (q : ℕ) (B : ℕ → ℕ) (r : ℕ) : ℕ :=
  r.factorial * (r.factorial * q ^ (r + 1)) *
    (1 + ∑ i ∈ Finset.range (r + 1), B i) ^ r

lemma reciprocal_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (B : ℕ → ℕ)
    (hB : ∀ r x, ‖iteratedFDeriv ℝ r f x‖ ≤ B r)
    (q : ℕ) (hq : 1 ≤ q) (hpos : ∀ x, 0 < f x) (hrecip : ∀ x, (f x)⁻¹ ≤ q)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (fun x => (f x)⁻¹) x‖ ≤ reciprocalBound q B r := by
  classical
  let D : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), (B i : ℝ)
  let C : ℝ := r.factorial * (q : ℝ) ^ (r + 1)
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
  have hd (i : ℕ) (hi : i ≤ r) : (B i : ℝ) ≤ D := by
    have h := Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun i => (B i : ℝ)) (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega : i < r + 1))
    dsimp [D]; linarith
  have hu : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Set.Ioi 0) :=
    (contDiffOn_inv ℝ).mono (by intro y hy; simpa using ne_of_gt hy)
  have h := norm_iteratedFDeriv_comp_le' (g := fun y : ℝ => y⁻¹) (f := f)
    (t := Set.Ioi 0) (fun y hy => by rcases hy with ⟨z, rfl⟩; exact hpos z)
    hu hinv hf (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) x (C := C) (D := D) ?_ ?_
  · simpa only [reciprocalBound, C, D, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_sum, Function.comp_def] using h
  · intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (contDiffAt_inv ℝ (hpos x).ne') (hpos x)]
    apply (inverse_jet_bound q i (hpos x) (hrecip x)).trans
    dsimp [C]
    push_cast
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hi
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (by omega)
    · positivity
    · positivity
  · intro i hi hir
    exact (hB i x).trans ((hd i hir).trans (le_self_pow₀ hD (by omega)))

noncomputable def transitionDenom (x : ℝ) : ℝ := expNegInvGlue x + expNegInvGlue (1 - x)

lemma transitionDenom_smooth : ContDiff ℝ ∞ transitionDenom :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma transitionDenom_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r transitionDenom x‖ ≤ (2 * rhoBound r : ℕ) := by
  have hs : ContDiff ℝ ∞ (fun x => expNegInvGlue (1 - x)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  unfold transitionDenom
  rw [fun_iteratedFDeriv_add_apply (expNegInvGlue.contDiff (n := ⊤) |>.of_le
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) |>.contDiffAt)
      (hs.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  apply (norm_add_le _ _).trans
  have h₂ : ‖iteratedFDeriv ℝ r (fun x => expNegInvGlue (1 - x)) x‖ ≤ rhoBound r := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_const_sub]
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using rho_jet_bound r (1 - x)
  have h₁ := rho_jet_bound r x
  push_cast
  linarith

def transitionInvBound (r : ℕ) : ℕ := reciprocalBound 9 (fun i => 2 * rhoBound i) r

lemma transitionInv_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (fun x => (transitionDenom x)⁻¹) x‖ ≤ transitionInvBound r := by
  apply reciprocal_jet_bound transitionDenom transitionDenom_smooth
    (fun i => 2 * rhoBound i) transitionDenom_bound 9 (by norm_num)
    (fun x => Real.smoothTransition.pos_denom x) _ r x
  intro x
  exact (inv_le_comm₀ (Real.smoothTransition.pos_denom x) (by norm_num : (0 : ℝ) < 9)).mpr
    (by simpa only [one_div] using transition_denom_lower x)

def transitionBound (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), r.choose i * rhoBound i * transitionInvBound (r - i)

lemma transition_jet_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r Real.smoothTransition x‖ ≤ transitionBound r := by
  have he : Real.smoothTransition = fun x => expNegInvGlue x * (transitionDenom x)⁻¹ := by
    funext x; simp only [Real.smoothTransition, transitionDenom, div_eq_mul_inv]
  rw [he]
  apply (norm_iteratedFDeriv_mul_le (expNegInvGlue.contDiff (n := ⊤))
    (transitionDenom_smooth.inv (fun x => (Real.smoothTransition.pos_denom x).ne')) x
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
  simp only [transitionBound, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul _ (transitionInv_bound (r - i) x) (norm_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (rho_jet_bound i x) (Nat.cast_nonneg _)

end Quantitative
end AlternatingNS

end QuantitativeDevelopment

end OAI
