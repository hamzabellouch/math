import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitKernelBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet

def smoothRightAbscissa (X : ℝ) : ℝ := 1+1/Real.log X

theorem smoothRightAbscissa_properties {X : ℝ} (hX : Real.exp 2 ≤ X) :
    1 ≤ X ∧ smoothRightAbscissa X ∈ Set.Ioc (1:ℝ) 2 ∧
      (smoothRightAbscissa X-1)⁻¹ = Real.log X ∧
      X^(smoothRightAbscissa X) = Real.exp 1*X := by
  have hXp : 0 < X := (Real.exp_pos 2).trans_le hX
  have hlog : 2 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hX
  have hlogp : 0 < Real.log X := by linarith
  have hXone : 1 ≤ X := by
    have : Real.exp 0 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have he : 1 ≤ Real.exp 2 := by simpa only [Real.exp_zero] using this
    exact he.trans hX
  refine ⟨hXone,⟨?_,?_⟩,?_,?_⟩
  · dsimp [smoothRightAbscissa]
    have hinv : 0 < 1/Real.log X := one_div_pos.mpr hlogp
    linarith
  · dsimp [smoothRightAbscissa]
    have : 1/Real.log X ≤ 1 := (div_le_one hlogp).mpr (by linarith)
    linarith
  · simp [smoothRightAbscissa]
  · rw [Real.rpow_def_of_pos hXp]
    have he : Real.log X*smoothRightAbscissa X = 1+Real.log X := by
      unfold smoothRightAbscissa
      field_simp
      ring
    rw [he,Real.exp_add,Real.exp_log hXp]

theorem contour_scale_ge_one {q : ℕ} [NeZero q] {T : ℝ} (hT : 2 ≤ T) :
    1 ≤ (q:ℝ)*(T+2) := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  nlinarith

theorem contour_vertical_length_le {q : ℕ} [NeZero q] {T : ℝ} (hT : 2 ≤ T) :
    2*T+2 ≤ 2*((q:ℝ)*(T+2)) := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  nlinarith

end Ostmann.Dirichlet

end

end OAI
