import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePropagation

namespace OAI

/-! Uniform dependence of the short free system on its coefficient and initial data. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialFreeField_parameter_norm (b c r : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hr : r ∈ Icc (3 : ℝ) (10/3)) (x y : ℂ × ℂ) :
    ‖radialFreeField b r x-radialFreeField c r y‖ ≤ 7*‖x-y‖+|b-c| *‖y‖ := by
  have he : radialFreeField b r x-radialFreeField c r y=
      radialFreeField b r (x-y)+(0,-((b-c : ℝ) : ℂ)*y.1) := by
    apply Prod.ext
    · dsimp [radialFreeField]; ring
    · dsimp [radialFreeField]; push_cast; ring
  have hn : ‖((0 : ℂ),-((b-c : ℝ) : ℂ)*y.1)‖ ≤ |b-c| *‖y‖ := by
    rw [Prod.norm_mk,norm_zero,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      max_eq_right (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (norm_fst_le y) (abs_nonneg _)
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (radialFreeField_norm b r hb hr (x-y)) hn)

theorem radial_free_state_parameter_bound (b c l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (X Y : ℝ → ℂ × ℂ) (hX : Continuous X) (hY : Continuous Y) (x₀ y₀ : ℂ × ℂ)
    (heX : ∀ r ∈ Icc l u, X r=x₀+∫ t in l..r, radialFreeField b t (X t))
    (heY : ∀ r ∈ Icc l u, Y r=y₀+∫ t in l..r, radialFreeField c t (Y t))
    (hYB : ∀ r ∈ Icc l u, ‖Y r‖ ≤ 2) :
    ∀ r ∈ Icc l u, ‖X r-Y r‖ ≤ 2*‖x₀-y₀‖+|b-c| := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlu)
    (hX.sub hY).norm.continuousOn
  let M := ‖X m-Y m‖
  have hM : 0 ≤ M := norm_nonneg _
  have hi (d : ℝ) (Z : ℝ → ℂ × ℂ) (hZ : Continuous Z) :
      IntervalIntegrable (fun t => radialFreeField d t (Z t)) volume l m :=
    ContinuousOn.intervalIntegrable_of_Icc hm.1
      ((radialFreeField_continuousOn_curve d l u (by linarith) Z hZ).mono
        (fun t ht => ⟨ht.1,ht.2.trans hm.2⟩))
  have he : X m-Y m=(x₀-y₀)+∫ t in l..m,
      radialFreeField b t (X t)-radialFreeField c t (Y t) := by
    rw [intervalIntegral.integral_sub (hi b X hX) (hi c Y hY),heX m hm,heY m hm]
    abel
  have hint : ‖∫ t in l..m, radialFreeField b t (X t)-radialFreeField c t (Y t)‖ ≤
      (7*M+2*|b-c|)*(m-l) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := m)
      (C := 7*M+2*|b-c|)
      (f := fun t => radialFreeField b t (X t)-radialFreeField c t (Y t)) (fun t ht => by
      have htI : t ∈ Icc l m := ⟨(uIoc_of_le hm.1 ▸ ht).1.le,(uIoc_of_le hm.1 ▸ ht).2⟩
      have htU : t ∈ Icc l u := ⟨htI.1,htI.2.trans hm.2⟩
      have hn := radialFreeField_parameter_norm b c t hb ⟨hl.trans htU.1,htU.2.trans hu⟩ (X t) (Y t)
      have hD : ‖X t-Y t‖ ≤ M := hmax htU
      have hYt := hYB t htU
      nlinarith [mul_le_mul_of_nonneg_left hYt (abs_nonneg (b-c))])
    simpa only [abs_of_nonneg (sub_nonneg.mpr hm.1)] using hh
  have hineq : M ≤ ‖x₀-y₀‖+(7*M+2*|b-c|)*(m-l) := calc
    M = ‖(x₀-y₀)+∫ t in l..m, radialFreeField b t (X t)-radialFreeField c t (Y t)‖ := congrArg norm he
    _ ≤ ‖x₀-y₀‖+‖∫ t in l..m, radialFreeField b t (X t)-radialFreeField c t (Y t)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hint
  have hlen : m-l ≤ (1/1000 : ℝ) := by linarith [hm.2]
  have hp := mul_le_mul_of_nonneg_left hlen (show 0 ≤ 7*M+2*|b-c| by positivity)
  have hbound : M ≤ 2*‖x₀-y₀‖+|b-c| := by nlinarith [norm_nonneg (x₀-y₀),abs_nonneg (b-c)]
  intro r hr
  exact (hmax hr).trans hbound

end DefocusingNLS

end OAI
