import OAI.Analysis.LipschitzHilbert.Phase.AngularPacketAmplitude
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Analytic transition weights for the shared angular packet family.
The exact modulus is the child-to-boundary mass ratio raised to the
real part of the corresponding complex parameter. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

def analyticTransition (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) : ℂ :=
  Complex.exp (phase level * (Real.log (mass (level + 1) cell / boundary level cell) : ℂ))

theorem analyticTransition_norm (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell) :
    ‖analyticTransition mass boundary phase level cell‖ =
      (mass (level + 1) cell / boundary level cell) ^ (phase level).re := by
  rw [analyticTransition, Complex.norm_exp, Real.rpow_def_of_pos (div_pos hm hb)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem analyticTransition_norm_le_one (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell)
    (hle : mass (level + 1) cell ≤ boundary level cell) (hphase : 0 ≤ (phase level).re) :
    ‖analyticTransition mass boundary phase level cell‖ ≤ 1 := by
  rw [analyticTransition_norm mass boundary phase level cell hm hb]
  exact Real.rpow_le_one (div_nonneg hm.le hb.le) ((div_le_one hb).mpr hle) hphase

theorem analyticTransition_entire (mass boundary : ℕ → ℤ → ℝ) (level : ℕ) (cell : ℤ) :
    Differentiable ℂ (fun z : ℂ =>
      Complex.exp (z * (Real.log (mass (level + 1) cell / boundary level cell) : ℂ))) := by
  fun_prop

theorem packetPathProduct_norm (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ)
    (hm : ∀ j ∈ Finset.Ico lower upper, 0 < mass (j + 1) (g.index (j + 1) slope))
    (hb : ∀ j ∈ Finset.Ico lower upper, 0 < boundary j (g.index (j + 1) slope)) :
    ‖g.packetPathProduct (analyticTransition mass boundary phase) lower upper slope‖ =
      ∏ j ∈ Finset.Ico lower upper,
        (mass (j + 1) (g.index (j + 1) slope) / boundary j (g.index (j + 1) slope)) ^
          (phase j).re := by
  rw [packetPathProduct, norm_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact analyticTransition_norm mass boundary phase j _ (hm j hj) (hb j hj)

end LipschitzHilbert.AngularGrid

end

end OAI
