import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Filter

theorem eventually_higherSource_loglog_sq_le_exp (k : ℕ) (α β : ℝ)
    (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      (Real.log (Real.log (higherSourceX k u:ℝ)))^2 ≤ ε*Real.exp (α*L) := by
  let C : ℝ := Real.log (1000*(4:ℝ)^k)
  let D : ℝ := |β|+|C|+1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 2 hα).const_mul_left (D^2)).bound hε
  have hgrowth := (tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  filter_upwards [hsmall,hgrowth,eventually_ge_atTop (1:ℝ)] with L hs hg hL
  simp only [id_eq] at hg
  intro u hul huu
  have hu : 0 ≤ u := by linarith
  have hb := higherSourceX_log_bounds k u hu
  have hlb := higherSourceX_loglog_bounds k u hu
  have hp : (1:ℝ) ≤ (4:ℝ)^k := one_le_pow₀ (by norm_num)
  have he : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hx1 : 1 ≤ Real.log (higherSourceX k u:ℝ) := by nlinarith [hb.2.1]
  have hx0 : 0 ≤ Real.log (Real.log (higherSourceX k u:ℝ)) := Real.log_nonneg hx1
  have hupper : Real.log (Real.log (higherSourceX k u:ℝ)) ≤ D*L := by
    have h1 : Real.log (Real.log (higherSourceX k u:ℝ)) ≤ β*L+C :=
      hlb.2.trans (add_le_add huu (le_refl C))
    have hβ := mul_le_mul_of_nonneg_right (le_abs_self β) (show 0 ≤ L by linarith)
    have hC := le_abs_self C
    have hCL := mul_le_mul_of_nonneg_left hL (abs_nonneg C)
    dsimp [D]
    nlinarith
  have hDL : 0 ≤ D*L := mul_nonneg hD (by linarith)
  have hs' : D^2*L^2 ≤ ε*Real.exp (α*L) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg L)),
      abs_of_pos (Real.exp_pos _)] using hs
  calc
    _ ≤ (D*L)^2 := by nlinarith
    _ = D^2*L^2 := by ring
    _ ≤ _ := hs'

theorem eventually_higherSource_loglog_sq_le_prime_log (k : ℕ) (α β : ℝ)
    (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u → u ≤ β*L → ∀ p : ℕ,
      Real.exp (α*L) ≤ Real.log (p:ℝ) →
      (Real.log (Real.log (higherSourceX k u:ℝ)))^2 ≤ ε*Real.log (p:ℝ) := by
  filter_upwards [eventually_higherSource_loglog_sq_le_exp k α β hα ε hε] with L hL
  intro u hul huu p hp
  exact (hL u hul huu).trans (mul_le_mul_of_nonneg_left hp hε.le)

end Ostmann.Characters

end

end OAI
