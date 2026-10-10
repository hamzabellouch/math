import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Filter
open scoped Topology

theorem supportRemoval_combine_of_one_le (K₁ K₂ : ℝ) {c₁ c₂ α₁ α₂ L : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL : 1 ≤ L) (z core : ℂ)
    (herr : ‖z-core‖ ≤ Real.exp (K₁*L^2-c₁*Real.exp (α₁*L)))
    (hcore : ‖core‖ ≤ Real.exp (K₂*L^2-c₂*Real.exp (α₂*L))) :
    ‖z‖ ≤ Real.exp ((max |K₁| |K₂|+1)*L^2-
      min c₁ c₂*Real.exp (min α₁ α₂*L)) := by
  have hL₀ : 0 ≤ L := le_trans (by norm_num) hL
  have hL₂ : 1 ≤ L^2 := by nlinarith
  have hdec₁ : min c₁ c₂*Real.exp (min α₁ α₂*L) ≤ c₁*Real.exp (α₁*L) := by
    exact mul_le_mul (min_le_left _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hL₀)) (Real.exp_pos _).le hc₁.le
  have hdec₂ : min c₁ c₂*Real.exp (min α₁ α₂*L) ≤ c₂*Real.exp (α₂*L) := by
    exact mul_le_mul (min_le_right _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hL₀)) (Real.exp_pos _).le hc₂.le
  have hK₁ : K₁*L^2 ≤ max |K₁| |K₂| *L^2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self K₁).trans (le_max_left _ _)) (sq_nonneg L)
  have hK₂ : K₂*L^2 ≤ max |K₁| |K₂| *L^2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self K₂).trans (le_max_right _ _)) (sq_nonneg L)
  let E := Real.exp (max |K₁| |K₂| *L^2-min c₁ c₂*Real.exp (min α₁ α₂*L))
  have he₁ : ‖z-core‖ ≤ E := herr.trans (Real.exp_le_exp.mpr (sub_le_sub hK₁ hdec₁))
  have he₂ : ‖core‖ ≤ E := hcore.trans (Real.exp_le_exp.mpr (sub_le_sub hK₂ hdec₂))
  have htwo : (2:ℝ) ≤ Real.exp (L^2) := by
    have hh := Real.add_one_le_exp (1:ℝ)
    have he := Real.exp_le_exp.mpr hL₂
    linarith
  calc
    ‖z‖ ≤ ‖z-core‖+‖core‖ := by simpa only [sub_add_cancel] using norm_add_le (z-core) core
    _ ≤ 2*E := by linarith
    _ ≤ Real.exp (L^2)*E := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp ((max |K₁| |K₂|+1)*L^2-min c₁ c₂*Real.exp (min α₁ α₂*L)) := by
      dsimp only [E]
      rw [← Real.exp_add]
      congr 1
      ring

theorem supportRemoval_combine_eventually (K₁ K₂ : ℝ) {c₁ c₂ α₁ α₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ∃ K > 0, ∃ c > 0, ∃ α > 0, ∀ᶠ L : ℝ in atTop, ∀ z core : ℂ,
      ‖z-core‖ ≤ Real.exp (K₁*L^2-c₁*Real.exp (α₁*L)) →
      ‖core‖ ≤ Real.exp (K₂*L^2-c₂*Real.exp (α₂*L)) →
      ‖z‖ ≤ Real.exp (K*L^2-c*Real.exp (α*L)) := by
  refine ⟨max |K₁| |K₂|+1,?_,min c₁ c₂,lt_min hc₁ hc₂,
    min α₁ α₂,lt_min hα₁ hα₂,?_⟩
  · have hh : 0 ≤ max |K₁| |K₂| := (abs_nonneg K₁).trans (le_max_left _ _)
    linarith
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  exact supportRemoval_combine_of_one_le K₁ K₂ hc₁ hc₂ hL

end Ostmann.Characters.DiagonalEstimate

end

end OAI
