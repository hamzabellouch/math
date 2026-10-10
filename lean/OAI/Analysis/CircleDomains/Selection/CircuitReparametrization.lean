import OAI.Analysis.CircleDomains.Topology.FiniteCircleStokes
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-! Changing the starting point or direction of a periodic circuit preserves
its image and the absolute value of its one-form integral. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem periodic_eq_of_close {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) (hi : InjOn f (Ico (0 : ℝ) 1))
    {x y : ℝ} (he : f x = f y) (hd : |x - y| < 1) : x = y := by
  have hx : f (Int.fract x) = f x := by
    simpa only [Int.fract, mul_one] using hp.sub_int_mul_eq (x := x) ⌊x⌋
  have hy : f (Int.fract y) = f y := by
    simpa only [Int.fract, mul_one] using hp.sub_int_mul_eq (x := y) ⌊y⌋
  have hh := hi ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩ (hx.trans (he.trans hy.symm))
  have hk : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) = x - y := by
    simp only [Int.fract, Int.cast_sub] at hh ⊢
    linarith
  have hb := abs_lt.mp hd
  have hklo : (-1 : ℤ) < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast (show (-1 : ℝ) < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) by rw [hk]; exact hb.1)
  have hkhi : ⌊x⌋ - ⌊y⌋ < (1 : ℤ) := by exact_mod_cast (show ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) < (1 : ℝ) by rw [hk]; exact hb.2)
  have hk0 : ⌊x⌋ - ⌊y⌋ = 0 := by omega
  rw [hk0, Int.cast_zero] at hk
  linarith

 theorem periodic_shift_injOn {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) (hi : InjOn f (Ico (0 : ℝ) 1)) (a : ℝ) :
    InjOn (fun t => f (a + t)) (Ico (0 : ℝ) 1) := by
  intro x hx y hy he
  have hh := periodic_eq_of_close hp hi he (show |(a + x) - (a + y)| < 1 by
    apply abs_lt.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  linarith

 theorem periodic_shift {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) (a : ℝ) :
    Function.Periodic (fun t => f (a + t)) 1 := by
  intro t
  simpa only [← add_assoc] using hp (a + t)

 theorem periodic_reverse {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) : Function.Periodic (fun t => f (1 - t)) 1 := by
  intro t
  change f (1 - (t + 1)) = f (1 - t)
  rw [show 1 - (t + 1) = (1 - t) - 1 by ring]
  exact hp.sub_eq (1 - t)

 theorem deriv_periodic {f : ℝ → ℂ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → ℂ => deriv g t) (funext hp)

 theorem planarFormIntegral_shift (P Q : ℂ → ℝ) {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) (a : ℝ) :
    planarFormIntegral P Q (fun t => γ (a + t)) = planarFormIntegral P Q γ := by
  let f : ℝ → ℝ := fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im
  have hfp : Function.Periodic f 1 := by
    intro t
    simp only [f, hp t, deriv_periodic hp t]
  have hd (t : ℝ) : deriv (fun s => γ (a + s)) t = deriv γ (a + t) := by
    exact deriv_comp_const_add γ a t
  change (∫ t in (0 : ℝ)..1, _) = ∫ t in (0 : ℝ)..1, f t
  simp_rw [hd]
  change (∫ t in (0 : ℝ)..1, f (a + t)) = _
  rw [intervalIntegral.integral_comp_add_left]
  simpa only [add_zero, zero_add] using hfp.intervalIntegral_add_eq a 0

 theorem planarFormIntegral_reverse (P Q : ℂ → ℝ) {γ : ℝ → ℂ}
    (hγ : Differentiable ℝ γ) :
    planarFormIntegral P Q (fun t => γ (1 - t)) = -planarFormIntegral P Q γ := by
  have hd (t : ℝ) : deriv (fun s => γ (1 - s)) t = -deriv γ (1 - t) := by
    simpa only [Function.comp_def, neg_one_smul] using
      ((hγ (1 - t)).hasDerivAt.scomp t ((hasDerivAt_id t).const_sub 1)).deriv
  unfold planarFormIntegral
  simp_rw [hd, Complex.neg_re, Complex.neg_im, mul_neg, ← neg_add]
  rw [intervalIntegral.integral_neg]
  change -(∫ t in (0 : ℝ)..1, (fun s => P (γ s) * (deriv γ s).re +
    Q (γ s) * (deriv γ s).im) (1 - t)) = _
  exact congrArg Neg.neg (by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (fun s : ℝ => P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im)
        (a := 0) (b := 1) (1 : ℝ))

 theorem circleFormIntegral_shift (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle)
    {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) (a : ℝ) :
    circleFormIntegral φ u (fun t => γ (a + t)) = circleFormIntegral φ u γ :=
  planarFormIntegral_shift _ _ hp a

 theorem circleFormIntegral_reverse (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle)
    {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) :
    circleFormIntegral φ u (fun t => γ (1 - t)) = -circleFormIntegral φ u γ :=
  planarFormIntegral_reverse _ _ hγ

end CircleDomainRigidity

end

end OAI
