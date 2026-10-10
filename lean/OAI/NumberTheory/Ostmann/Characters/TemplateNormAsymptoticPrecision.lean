import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetModulus

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateNormAsymptotic
open Filter HistoryFrequencyBudget HistoryFrequencyLabels

theorem word_tendsto {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L : ℝ => (⌊z*L⌋₊ : ℝ)) atTop atTop := by
  have ht : Tendsto (fun L : ℝ => z*L-1) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      (tendsto_id.const_mul_atTop hz).atTop_add (tendsto_const_nhds (x := -(1 : ℝ)))
  apply tendsto_atTop_mono _ ht
  intro L
  have h := Nat.lt_floor_add_one (z*L)
  linarith

theorem linear_lt_prime_log_eventually {z α : ℝ} (hz : 0 < z) (hα : 0 < α)
    (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, D*(⌊z*L⌋₊ : ℝ) < Real.exp (α*L) := by
  have hdom := (tendsto_exp_mul_div_rpow_atTop 1 α hα).eventually_gt_atTop (D*z)
  filter_upwards [hdom,eventually_ge_atTop (1 : ℝ)] with L hdom hL
  have hLp : 0 < L := by linarith
  have hm := Nat.floor_le (mul_nonneg hz.le hLp.le)
  have hlin : D*z*L < Real.exp (α*L) := by
    simp only [Real.rpow_one] at hdom
    exact (lt_div_iff₀ hLp).mp hdom
  exact (mul_le_mul_of_nonneg_left hm hD).trans_lt (by simpa only [mul_assoc] using hlin)

theorem precision_lt_prime_eventually {z α a : ℝ} (hz : 0 < z) (hα : 0 < α)
    (ha : 0 ≤ a) (j K : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ s : ℤ, ∀ t : HistoryReconstruction.Tree j,
      RangeSupported (ranges a (⌊z*L⌋₊ : ℝ) j) j [] s t →
      ∀ p : ℕ, p.Prime → Real.exp (α*L) ≤ Real.log p →
      (modulus j [] s t)^(K+2) < p := by
  let D : ℝ := (K+2:ℕ)*((2^(j+1)-1:ℕ):ℝ)*linearEnvelope a j
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (by positivity) (linearEnvelope_pos ha j).le
  filter_upwards [linear_lt_prime_log_eventually hz hα D hD,
    (word_tendsto hz).eventually_ge_atTop 1] with L hL hm
  intro s t ht p hp hlog
  have hmod := supported_precision_le_exp ha hm ht K
  have hlt : D*(⌊z*L⌋₊ : ℝ) < Real.log p := hL.trans_le hlog
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hreal : (((modulus j [] s t)^(K+2) : ℕ) : ℝ) < (p:ℝ) := by
    exact hmod.trans_lt (by simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr hlt)
  exact_mod_cast hreal

end Ostmann.Characters.TemplateNormAsymptotic

end

end OAI
