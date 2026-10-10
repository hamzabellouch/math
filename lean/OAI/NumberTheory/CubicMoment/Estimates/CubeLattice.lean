import OAI.NumberTheory.CubicMoment.Estimates.CubeSummation
import OAI.NumberTheory.CubicMoment.Estimates.NormSeries
import OAI.NumberTheory.CubicGram.MellinDecay

namespace OAI

/-!
# The convergent cube lattice in dispersion

Rapid decay of the actual radial Fourier profile justifies the cube
regrouping. The factor one third is proved from the arithmetic fibers.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_norm_pow (a : Eisenstein) (n : ℕ) : norm (a^n) = (norm a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

/-- Decay of the Fourier profile makes the cube lattice absolutely
summable for every positive scale. -/
theorem summable_radial_cube_lattice (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : Eisenstein => radialDualProfile W (c*(norm j)^3)) := by
  obtain ⟨C,hC,hbound⟩ := radialDualProfile_rapidDecay W hW hW' 1
  apply ((summable_eisenstein_norm_rpow (s := 3) (by norm_num)).mul_left (C/c)).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : Eisenstein)] with j hj
  have hn := norm_pos_of_ne_zero hj
  have hp : 0 < c*(norm j)^3 := by positivity
  have hb := hbound (c*(norm j)^3) hp.le
  simp only [pow_one] at hb
  have hb' : ‖radialDualProfile W (c*(norm j)^3)‖*(c*(norm j)^3) ≤ C := by
    nlinarith [_root_.norm_nonneg (radialDualProfile W (c*(norm j)^3))]
  calc
    _ ≤ C/(c*(norm j)^3) := (le_div_iff₀ hp).mpr hb'
    _ = (C/c)*norm j^(-(3:ℝ)) := by
      rw [Real.rpow_neg hn.le,Real.rpow_ofNat]
      field_simp

/-- The exact normalized cube-frequency sum, with the origin removed. -/
theorem radial_cube_lattice_sum (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {c : ℝ} (hc : 0 < c) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      radialDualProfile W (c*norm h) else 0) =
      (1/3:ℂ)*(∑' j : Eisenstein, if j = 0 then 0 else
        radialDualProfile W (c*(norm j)^3)) := by
  have hs : Summable (fun j : Eisenstein => if j = 0 then (0:ℂ) else
      radialDualProfile W (c*norm (j^3))) := by
    apply (summable_radial_cube_lattice W hW hW' hc).norm.of_norm_bounded
    intro j
    by_cases hj : j = 0
    · simp only [ite_eq_left hj,norm_zero]
      exact _root_.norm_nonneg _
    · rw [ite_eq_right hj,eisenstein_norm_pow]
  have he := tsum_nonzero_cubes (fun h => radialDualProfile W (c*norm h)) hs
  simp only [eisenstein_norm_pow] at he
  linear_combination -(1/3:ℂ)*he

end CubicFirstMoment

end

end OAI
