import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace OAI

/-! Dyadic slope energies for the quantitative differentiation of the
planar branching profile. Only the Lipschitz constant two is needed. -/
namespace Falconer

noncomputable def intervalSecantSlope (f : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (f (a+h)-f a)/h

theorem intervalSecantSlope_abs_le {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) : |intervalSecantSlope f a h| ≤ 2 := by
  have hd := hf.dist_le_mul (a+h) a
  rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at hd
  unfold intervalSecantSlope
  rw [abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).2 hd

theorem intervalSecantSlope_children (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : h ≠ 0) :
    intervalSecantSlope f a (h/2)+intervalSecantSlope f (a+h/2) (h/2) =
      2*intervalSecantSlope f a h := by
  unfold intervalSecantSlope
  rw [show a+h/2+h/2 = a+h by ring]
  field_simp [hh]
  ring

noncomputable def dyadicSlopeEnergy (f : ℝ → ℝ) (a h : ℝ) : ℕ → ℝ
  | 0 => (intervalSecantSlope f a h)^2
  | n+1 => (dyadicSlopeEnergy f a (h/2) n + dyadicSlopeEnergy f (a+h/2) (h/2) n)/2

theorem dyadicSlopeEnergy_nonneg (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    0 ≤ dyadicSlopeEnergy f a h n := by
  induction n generalizing a h with
  | zero => exact sq_nonneg _
  | succ n ih => exact div_nonneg (add_nonneg (ih _ _) (ih _ _)) (by norm_num)

theorem dyadicSlopeEnergy_le_four {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) : dyadicSlopeEnergy f a h n ≤ 4 := by
  induction n generalizing a h with
  | zero =>
    have hb := intervalSecantSlope_abs_le hf a hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hb
    simpa only [dyadicSlopeEnergy,sq_abs,show (2:ℝ)^2 = 4 by norm_num] using hsq
  | succ n ih =>
    have h₁ := ih a (half_pos hh)
    have h₂ := ih (a+h/2) (half_pos hh)
    change (_+_)/2 ≤ 4
    linarith

theorem dyadicSlopeEnergy_step_mono (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) : dyadicSlopeEnergy f a h n ≤ dyadicSlopeEnergy f a h (n+1) := by
  induction n generalizing a h with
  | zero =>
    have he := intervalSecantSlope_children f a hh.ne'
    have hs := sq_nonneg (intervalSecantSlope f a (h/2)-intervalSecantSlope f (a+h/2) (h/2))
    change (intervalSecantSlope f a h)^2 ≤
      ((intervalSecantSlope f a (h/2))^2+(intervalSecantSlope f (a+h/2) (h/2))^2)/2
    have he2 := congrArg (fun x : ℝ => x^2) he
    nlinarith
  | succ n ih =>
    have h₁ := ih a (half_pos hh)
    have h₂ := ih (a+h/2) (half_pos hh)
    change (_+_)/2 ≤ (_+_)/2
    linarith

theorem dyadicSlopeEnergy_mono (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    Monotone (dyadicSlopeEnergy f a h) :=
  monotone_nat_of_le_succ (dyadicSlopeEnergy_step_mono f a hh)

end Falconer

end OAI
