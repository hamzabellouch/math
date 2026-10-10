import OAI.Analysis.LipschitzHilbert.Fourier.LineLpDerivative
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

namespace OAI

/-! An integrable common envelope for bounded displacements of a line
Schwartz function, used to pass to nonsmooth directions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzDecayConstant (f : SchwartzMap ℝ ℂ) : ℝ :=
  4*(Finset.Iic (2,0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

theorem lineSchwartzDecayConstant_nonneg (f : SchwartzMap ℝ ℂ) :
    0≤lineSchwartzDecayConstant f := mul_nonneg (by norm_num) (apply_nonneg _ _)

theorem lineSchwartz_decay (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    (1+|y|)^2*‖f y‖≤lineSchwartzDecayConstant f := by
  have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ) (m:=(2,0))
    (k:=2) (n:=0) (by rfl) (by rfl) f y
  simpa only [lineSchwartzDecayConstant,norm_iteratedFDeriv_zero,Real.norm_eq_abs,show (2:ℝ)^2=4 by norm_num] using hh

theorem lineSchwartz_shift_decay (f : SchwartzMap ℝ ℂ) (y d : ℝ) (hd : |d|≤1) :
    ‖f (y-d)‖≤4*lineSchwartzDecayConstant f/(1+|y|)^2 := by
  have hgeom : 1+|y|≤2*(1+|y-d|) := by
    have hh := abs_add_le (y-d) d
    rw [sub_add_cancel] at hh
    linarith [abs_nonneg (y-d)]
  have hs : (1+|y|)^2≤4*(1+|y-d|)^2 := by
    simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0≤1+|y|) hgeom 2
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    ‖f (y-d)‖*(1+|y|)^2 ≤ ‖f (y-d)‖*(4*(1+|y-d|)^2) :=
      mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = 4*((1+|y-d|)^2*‖f (y-d)‖) := by ring
    _ ≤ 4*lineSchwartzDecayConstant f := mul_le_mul_of_nonneg_left (lineSchwartz_decay f (y-d)) (by norm_num)

theorem lineSchwartz_shift_envelope_integrable (f : SchwartzMap ℝ ℂ) :
    Integrable (fun y : ℝ => (8*lineSchwartzDecayConstant f/(1+|y|)^2)^2) := by
  have hi : Integrable (fun y : ℝ => ((1+|y|)^4)⁻¹) := by
    have hh := integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=4) (by norm_num)
    simpa only [Real.norm_eq_abs,show (- (4:ℝ))=(-(4:ℕ):ℝ) by norm_num,
      Real.rpow_neg_natCast,zpow_neg,zpow_natCast] using hh
  convert hi.const_mul ((8*lineSchwartzDecayConstant f)^2) using 1
  ext y
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
