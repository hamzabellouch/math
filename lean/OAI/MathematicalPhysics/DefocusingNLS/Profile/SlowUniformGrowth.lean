import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowParameterHolomorphy

namespace OAI

/-! # Uniform spatial growth on compact parameter sets -/

open MeasureTheory

namespace DefocusingNLS

theorem norm_cpow_uniform_lower_bound (x q : ℂ) (δ A : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ ‖x‖) (hA : 0 ≤ A) (hq : ‖q‖ ≤ A) :
    ‖x ^ (-q)‖ ≤ Real.exp (Real.pi * A) * (1 + δ ^ (-A)) * (1 + ‖x‖) ^ A := by
  have hxpos : 0 < ‖x‖ := hδ.trans_le hx
  have hqa : -A ≤ q.re ∧ q.re ≤ A := by
    have h := (Complex.abs_re_le_norm q).trans hq
    exact abs_le.mp h
  have hp : ‖x‖ ^ (-q.re) ≤ (1 + δ ^ (-A)) * (1 + ‖x‖) ^ A := by
    rcases le_total 1 ‖x‖ with hn | hn
    · have h₁ := Real.rpow_le_rpow_of_exponent_le hn (show -q.re ≤ A by linarith)
      have h₂ := Real.rpow_le_rpow (norm_nonneg x) (by linarith : ‖x‖ ≤ 1 + ‖x‖) hA
      exact (h₁.trans h₂).trans (le_mul_of_one_le_left (by positivity)
        (le_add_of_nonneg_right (Real.rpow_nonneg hδ.le _)))
    · have h₁ := Real.rpow_le_rpow_of_exponent_ge hxpos hn (show -A ≤ -q.re by linarith)
      have h₂ := Real.rpow_le_rpow_of_nonpos hδ hx (neg_nonpos.mpr hA)
      have h₃ : 1 ≤ (1 + ‖x‖) ^ A := Real.one_le_rpow (by linarith [norm_nonneg x]) hA
      calc
        _ ≤ δ ^ (-A) := h₁.trans h₂
        _ ≤ 1 + δ ^ (-A) := by linarith
        _ ≤ _ := le_mul_of_one_le_right (by positivity) h₃
  have hi : -(x.arg * (-q).im) ≤ Real.pi * A := by
    calc
      _ ≤ |x.arg * (-q).im| := neg_le_abs _
      _ = |x.arg| * |q.im| := by simp only [Complex.neg_im, abs_mul, abs_neg]
      _ ≤ Real.pi * A := mul_le_mul (Complex.abs_arg_le_pi x)
        ((Complex.abs_im_le_norm q).trans hq) (abs_nonneg _) Real.pi_pos.le
  calc
    _ ≤ ‖x‖ ^ (-q.re) * Real.exp (-(x.arg * (-q).im)) := by
      simpa only [Complex.neg_re, div_eq_mul_inv, ← Real.exp_neg] using Complex.norm_cpow_le x (-q)
    _ ≤ ((1 + δ ^ (-A)) * (1 + ‖x‖) ^ A) * Real.exp (Real.pi * A) :=
      mul_le_mul hp (Real.exp_le_exp.mpr hi) (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

noncomputable def slowParameterMajorant (a b M : ℝ) (u : ℝ) : ℝ :=
  Real.exp (-u) * u ^ a + Real.exp (-u) * u ^ b +
    Real.exp (-u) * u ^ (a + (M + 1)) + Real.exp (-u) * u ^ (b + (M + 1))

theorem integrable_slowParameterMajorant (a b M : ℝ)
    (ha : -1 < a) (hab : a ≤ b) (hM : 0 ≤ M) :
    IntegrableOn (slowParameterMajorant a b M) (Set.Ioi 0) := by
  exact (((integrable_exp_neg_mul_rpow a ha).add
    (integrable_exp_neg_mul_rpow b (ha.trans_le hab))).add
      (integrable_exp_neg_mul_rpow (a + (M + 1)) (by linarith))).add
        (integrable_exp_neg_mul_rpow (b + (M + 1)) (by linarith))

theorem regularizedSlowKernel_uniform_spatial_bound (q : ℂ) (m : ℕ) (x : ℂ)
    (a b M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hqa : a ≤ q.re) (hqb : q.re ≤ b)
    (hqm : ‖(m : ℂ) - 1 - q‖ ≤ M) (hx : 0 ≤ x.re) (hxδ : δ ≤ ‖x‖)
    {u : ℝ} (hu : 0 < u) :
    ‖regularizedSlowKernel q m x u‖ ≤
      (M * Real.exp (Real.pi * M) / δ * (1 + δ⁻¹) ^ (M + 1)) *
        slowParameterMajorant a b M u := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hδ.trans_le hxδ).ne'
  apply (regularizedSlowKernel_bounded_parameters q m x a b M hM hqa hqb hqm hx hx0 hu).trans
  change _ ≤ _ * (Real.exp (-u) * u ^ a + Real.exp (-u) * u ^ b +
    Real.exp (-u) * u ^ (a + (M + 1)) + Real.exp (-u) * u ^ (b + (M + 1)))
  gcongr

/-- Bounded parameters and a spatial distance from zero give one polynomial
bound valid on the whole closed right half-plane. -/
theorem exists_regularizedSlowSolution_uniform_bound (m : ℕ) (a b M δ A G : ℝ)
    (ha : -1 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q x : ℂ,
      a ≤ q.re → q.re ≤ b → ‖(m : ℂ) - 1 - q‖ ≤ M → ‖q‖ ≤ A →
      ‖(Complex.Gamma q)⁻¹‖ ≤ G → 0 ≤ x.re → δ ≤ ‖x‖ →
        ‖regularizedSlowSolution q m x‖ ≤ C * (1 + ‖x‖) ^ A := by
  let K := M * Real.exp (Real.pi * M) / δ * (1 + δ⁻¹) ^ (M + 1)
  let I := ‖∫ u : ℝ in Set.Ioi 0, slowParameterMajorant a b M u‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hI : 0 ≤ I := norm_nonneg _
  refine ⟨Real.exp (Real.pi * A) * (1 + δ ^ (-A)) * (1 + G * (K * I)), by positivity, ?_⟩
  intro q x hqa hqb hqm hq hγ hx hxδ
  have hi : ‖∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u‖ ≤ K * I := by
    calc
      _ ≤ ∫ u : ℝ in Set.Ioi 0, K * slowParameterMajorant a b M u := by
        apply norm_integral_le_of_norm_le ((integrable_slowParameterMajorant a b M ha hab hM).const_mul K)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact regularizedSlowKernel_uniform_spatial_bound q m x a b M δ hM hδ hqa hqb hqm hx hxδ hu
      _ = K * ∫ u : ℝ in Set.Ioi 0, slowParameterMajorant a b M u := integral_const_mul _ _
      _ ≤ K * I := mul_le_mul_of_nonneg_left (by dsimp only [I]; rw [Real.norm_eq_abs]; exact le_abs_self _) hK
  have hb : ‖1 + (Complex.Gamma q)⁻¹ *
      ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u‖ ≤ 1 + G * (K * I) := by
    apply (norm_add_le _ _).trans
    rw [norm_one, norm_mul]
    exact add_le_add le_rfl (mul_le_mul hγ hi (norm_nonneg _) hG)
  unfold regularizedSlowSolution
  rw [norm_mul]
  calc
    _ ≤ (Real.exp (Real.pi * A) * (1 + δ ^ (-A)) * (1 + ‖x‖) ^ A) *
        (1 + G * (K * I)) :=
      mul_le_mul (norm_cpow_uniform_lower_bound x q δ A hδ hxδ hA hq) hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI
