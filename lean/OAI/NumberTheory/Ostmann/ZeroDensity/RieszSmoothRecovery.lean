import Mathlib.Analysis.Calculus.MeanValue
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszPositiveRecovery

namespace OAI

/-! # Positive unsmoothing with a twice differentiable main term -/

namespace Ostmann

open Set
open scoped BigOperators

theorem smooth_main_remainder_pair (F f f' : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hF : ∀ t ∈ Icc (x - h) (x + h), HasDerivAt F (f t) t)
    (hf : ∀ t ∈ Icc (x - h) (x + h), HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc (x - h) (x + h), |f' t| ≤ 2) :
    |F (x + h) - F x - h * f x| ≤ 2 * h ^ 2 ∧
      |F x - F (x - h) - h * f x| ≤ 2 * h ^ 2 := by
  let K := Icc (x - h) (x + h)
  have hx : x ∈ K := ⟨by linarith, by linarith⟩
  have hp : x + h ∈ K := ⟨by linarith, le_rfl⟩
  have hm : x - h ∈ K := ⟨le_rfl, by linarith⟩
  have hlocal (t : ℝ) (ht : t ∈ K) : ‖f t - f x‖ ≤ 2 * h := by
    have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hf y hy).hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hb y hy)
      (convex_Icc (x - h) (x + h)) hx ht
    have ha : |t - x| ≤ h := abs_le.mpr ⟨by have := ht.1; linarith, by have := ht.2; linarith⟩
    simpa only [Real.norm_eq_abs] using hl.trans (mul_le_mul_of_nonneg_left ha (by norm_num))
  let G : ℝ → ℝ := fun t => F t - f x * t
  have hg (t : ℝ) (ht : t ∈ K) : HasDerivAt G (f t - f x) t := by
    have hh := (hF t ht).sub ((hasDerivAt_id t).const_mul (f x))
    change HasDerivAt (fun y => F y - f x * y) (f t - f x * 1) t at hh
    simpa only [mul_one] using hh
  have hplus := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hlocal (convex_Icc (x - h) (x + h)) hx hp
  have hminus := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hlocal (convex_Icc (x - h) (x + h)) hm hx
  have hep : G (x + h) - G x = F (x + h) - F x - h * f x := by dsimp [G]; ring
  have hem : G x - G (x - h) = F x - F (x - h) - h * f x := by dsimp [G]; ring
  rw [hep, Real.norm_eq_abs, show x + h - x = h by ring, Real.norm_eq_abs,
    abs_of_pos hh] at hplus
  rw [hem, Real.norm_eq_abs, show x - (x - h) = h by ring, Real.norm_eq_abs,
    abs_of_pos hh] at hminus
  exact ⟨by nlinarith, by nlinarith⟩

theorem finiteRieszSum_smooth_recovery (S : Finset ℕ) (w : ℕ → ℝ)
    (F : ℝ → ℝ) (x h m E : ℝ) (hh : 0 < h) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hzero : |finiteRieszSum S w x - F x| ≤ E)
    (hplus : |finiteRieszSum S w (x + h) - F (x + h)| ≤ E)
    (hminus : |finiteRieszSum S w (x - h) - F (x - h)| ≤ E)
    (hFplus : |F (x + h) - F x - h * m| ≤ 2 * h ^ 2)
    (hFminus : |F x - F (x - h) - h * m| ≤ 2 * h ^ 2) :
    |(∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - m| ≤ 2 * h + 2 * E / h := by
  have hb := finiteRieszSum_recover S w x h m (2 * h ^ 2 + 2 * E) hh hw
    (by have ha := (abs_le.mp hplus).2; have hc := (abs_le.mp hzero).1
        have hf := (abs_le.mp hFplus).2; linarith)
    (by have ha := (abs_le.mp hminus).2; have hc := (abs_le.mp hzero).1
        have hf := (abs_le.mp hFminus).1; linarith)
  convert hb using 1
  field_simp

end Ostmann

end OAI
