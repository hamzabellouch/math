import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorPowers
import OAI.NumberTheory.CubicMoment.Estimates.ExceptionalExponents

namespace OAI

/-! Logarithmic exponents of actual positive sequences and the limits
of the proved moment inequalities. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace CubicFirstMoment

def HasPowerExponent (Y f : ℕ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun j => Real.log (f j)/Real.log (Y j)) atTop (𝓝 a)

theorem HasPowerExponent.const {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop)
    (C : ℝ) : HasPowerExponent Y (fun _ => C) 0 :=
  (Real.tendsto_log_atTop.comp hY).const_div_atTop _

theorem HasPowerExponent.mul {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j) :
    HasPowerExponent Y (fun j => f j*g j) (a+b) := by
  apply (hf.add hg).congr'
  filter_upwards [hfp,hgp] with j hfj hgj
  simp only [Real.log_mul hfj.ne' hgj.ne',add_div]

theorem HasPowerExponent.rpow {Y f : ℕ → ℝ} {a : ℝ}
    (hf : HasPowerExponent Y f a) (hfp : ∀ᶠ j in atTop, 0 < f j) (p : ℝ) :
    HasPowerExponent Y (fun j => (f j)^p) (p*a) := by
  apply (hf.const_mul p).congr'
  filter_upwards [hfp] with j hfj
  simp only [Real.log_rpow hfj,mul_div_assoc]

theorem HasPowerExponent.natPow {Y f : ℕ → ℝ} {a : ℝ}
    (hf : HasPowerExponent Y f a) (k : ℕ) :
    HasPowerExponent Y (fun j => (f j)^k) ((k:ℝ)*a) := by
  apply (hf.const_mul (k:ℝ)).congr'
  filter_upwards [] with j
  simp only [Real.log_pow,mul_div_assoc]

private lemma log_max_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (max x y) = max (Real.log x) (Real.log y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h,max_eq_right (Real.log_le_log hx h)]
  · rw [max_eq_left h,max_eq_left (Real.log_le_log hy h)]

theorem HasPowerExponent.add {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hY : Tendsto Y atTop atTop)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j) :
    HasPowerExponent Y (fun j => f j+g j) (max a b) := by
  have hmax : HasPowerExponent Y (fun j => max (f j) (g j)) (max a b) := by
    apply (hf.max hg).congr'
    filter_upwards [hY.eventually_gt_atTop 1,hfp,hgp] with j hYj hfj hgj
    rw [log_max_pos hfj hgj,← max_div_div_right (Real.log_pos hYj).le]
  have hu : Tendsto
      (fun j => Real.log 2/Real.log (Y j)+Real.log (max (f j) (g j))/Real.log (Y j))
      atTop (𝓝 (max a b)) := by
    simpa only [zero_add,Function.comp_def] using ((Real.tendsto_log_atTop.comp hY).const_div_atTop
      (Real.log 2)).add hmax
  apply hmax.squeeze' hu
  · filter_upwards [hY.eventually_gt_atTop 1,hfp,hgp] with j hYj hfj hgj
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    exact Real.log_le_log (lt_max_of_lt_left hfj) (max_le (by linarith) (by linarith))
  · filter_upwards [hY.eventually_gt_atTop 1,hfp,hgp] with j hYj hfj hgj
    rw [← add_div,← Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (ne_of_gt (lt_max_of_lt_left hfj))]
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    apply Real.log_le_log (add_pos hfj hgj)
    have hfmax := le_max_left (f j) (g j)
    have hgmax := le_max_right (f j) (g j)
    linarith

theorem HasPowerExponent.mono {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hY : Tendsto Y atTop atTop)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hle : ∀ᶠ j in atTop, f j ≤ g j) : a ≤ b := by
  apply le_of_tendsto_of_tendsto hf hg
  filter_upwards [hY.eventually_gt_atTop 1,hfp,hle] with j hYj hfj hle
  exact div_le_div_of_nonneg_right (Real.log_le_log hfj hle) (Real.log_pos hYj).le

private lemma remove_positive_loss {a b c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ε*c+b) : a ≤ b := by
  by_contra hab
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  let ε : ℝ := (a-b)/(2*(|c|+1))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have he : ε*(2*(|c|+1)) = a-b := div_mul_cancel₀ _ (by positivity)
  have hc := mul_le_mul_of_nonneg_left (le_abs_self c) hε.le
  have hb := h ε hε
  nlinarith [mul_nonneg hε.le (abs_nonneg c)]

/-- Taking actual logarithmic limits of the sharp cubic moment gives
the numerical inequality used in the first exceptional configuration. -/
theorem cubic_moment_exponent {Y R V N L : ℕ → ℝ} {r v n z : ℝ}
    (hY : Tendsto Y atTop atTop)
    (hRp : ∀ᶠ j in atTop, 0 < R j) (hVp : ∀ᶠ j in atTop, 0 < V j)
    (hNp : ∀ᶠ j in atTop, 0 < N j) (hLp : ∀ᶠ j in atTop, 0 < L j)
    (hR : HasPowerExponent Y R r) (hV : HasPowerExponent Y V v)
    (hN : HasPowerExponent Y N n) (hL : HasPowerExponent Y L z)
    (hmoment : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j in atTop, R j*(V j)^2 ≤
        C*(N j*L j)^ε*L j*(N j+L j+(N j*L j)^(2/3:ℝ))) :
    r+2*v ≤ z+max (max n z) ((2/3:ℝ)*(n+z)) := by
  apply remove_positive_loss (c := n+z)
  intro ε hε
  obtain ⟨C,hC,hm⟩ := hmoment ε hε
  have hNL := hN.mul hL hNp hLp
  have hNLp : ∀ᶠ j in atTop, 0 < N j*L j := by
    filter_upwards [hNp,hLp] with j hn hl using mul_pos hn hl
  have hsum := (hN.add hL hY hNp hLp).add (hNL.rpow hNLp (2/3:ℝ)) hY
    (by filter_upwards [hNp,hLp] with j hn hl using add_pos hn hl)
    (by filter_upwards [hNLp] with j h using Real.rpow_pos_of_pos h _)
  have hleft := hR.mul (hV.natPow 2) hRp
    (by filter_upwards [hVp] with j h using sq_pos_of_pos h)
  have hright := (((HasPowerExponent.const hY C).mul (hNL.rpow hNLp ε)
    (Eventually.of_forall (fun _ => hC))
    (by filter_upwards [hNLp] with j h using Real.rpow_pos_of_pos h _)).mul hL
    (by filter_upwards [hNLp] with j h using mul_pos hC (Real.rpow_pos_of_pos h _)) hLp).mul hsum
    (by filter_upwards [hNLp,hLp] with j h hl using mul_pos (mul_pos hC
      (Real.rpow_pos_of_pos h _)) hl)
    (by filter_upwards [hNp,hLp,hNLp] with j hn hl h using
      add_pos (add_pos hn hl) (Real.rpow_pos_of_pos h _))
  have h := hleft.mono hright hY
    (by filter_upwards [hRp,hVp] with j hr hv using mul_pos hr (sq_pos_of_pos hv)) hm
  simpa only [Nat.cast_ofNat,zero_add,add_assoc] using h

/-- The ordinary mixed-character moment gives the second configuration's
limiting exponent, again by taking limits of actual inequalities. -/
theorem ordinary_moment_exponent {Y R V Q L : ℕ → ℝ} {r v q z : ℝ}
    (hY : Tendsto Y atTop atTop)
    (hRp : ∀ᶠ j in atTop, 0 < R j) (hVp : ∀ᶠ j in atTop, 0 < V j)
    (hQp : ∀ᶠ j in atTop, 0 < Q j) (hLp : ∀ᶠ j in atTop, 0 < L j)
    (hR : HasPowerExponent Y R r) (hV : HasPowerExponent Y V v)
    (hQ : HasPowerExponent Y Q q) (hL : HasPowerExponent Y L z)
    (hmoment : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j in atTop, R j*(V j)^2 ≤ C*(Q j*L j)^ε*L j*((Q j)^2+L j)) :
    r+2*v ≤ z+max (2*q) z := by
  apply remove_positive_loss (c := q+z)
  intro ε hε
  obtain ⟨C,hC,hm⟩ := hmoment ε hε
  have hQL := hQ.mul hL hQp hLp
  have hQLp : ∀ᶠ j in atTop, 0 < Q j*L j := by
    filter_upwards [hQp,hLp] with j hq hl using mul_pos hq hl
  have hsum := (hQ.natPow 2).add hL hY
    (by filter_upwards [hQp] with j hq using sq_pos_of_pos hq) hLp
  have hleft := hR.mul (hV.natPow 2) hRp
    (by filter_upwards [hVp] with j h using sq_pos_of_pos h)
  have hright := (((HasPowerExponent.const hY C).mul (hQL.rpow hQLp ε)
    (Eventually.of_forall (fun _ => hC))
    (by filter_upwards [hQLp] with j h using Real.rpow_pos_of_pos h _)).mul hL
    (by filter_upwards [hQLp] with j h using mul_pos hC (Real.rpow_pos_of_pos h _)) hLp).mul hsum
    (by filter_upwards [hQLp,hLp] with j h hl using mul_pos (mul_pos hC
      (Real.rpow_pos_of_pos h _)) hl)
    (by filter_upwards [hQp,hLp] with j hq hl using add_pos (sq_pos_of_pos hq) hl)
  have h := hleft.mono hright hY
    (by filter_upwards [hRp,hVp] with j hr hv using mul_pos hr (sq_pos_of_pos hv)) hm
  simpa only [Nat.cast_ofNat,zero_add,add_assoc] using h

end CubicFirstMoment

end

end OAI
