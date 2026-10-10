import OAI.MeasureTheory.Falconer.Shells.SpatialSharedShell
import OAI.MeasureTheory.Falconer.Shells.SmoothShellDomination

namespace OAI

/-! # The dimension-exact scalar to angular shell normalization

The one-dimensional shell comparison is independent of ambient dimension.
The stationary factor contributes exactly the remaining d-1 powers.
-/

namespace Falconer
open Set MeasureTheory

theorem scalar_angular_shell_normalization (d : ℕ) (a v : ℝ) :
    (2:ℝ)^(-a)*(2:ℝ)^v*((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2 =
      (2:ℝ)^((d:ℝ)*(v-a)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num),← Real.rpow_add (by norm_num)]
  congr 1
  ring

theorem scalar_shell_from_angular_energy (d : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hsupp : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hbF : ∀ r, ‖F r‖ ≤ C) {H : ℝ}
    (hH : (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ H) :
    (2:ℝ)^(-a)*
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
        ‖(((2:ℝ)^((v-a)*((d:ℝ)-1)/2) : ℝ) : ℂ)*F r‖^2) ≤ H := by
  have hp : 0 ≤ (2:ℝ)^((v-a)*((d:ℝ)-1)/2) := by positivity
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,mul_pow,
    integral_const_mul]
  have hdom := PlanarFalconer.dyadic_shell_smooth_domination v Ψ hΨ hpos hsupp hW hΨW hone
    F hF hC hbF
  calc
    _ ≤ (2:ℝ)^(-a)*(((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*
        ((2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdom (sq_nonneg _)) (by positivity)
    _ = (2:ℝ)^((d:ℝ)*(v-a)) *
        (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
      rw [show (2:ℝ)^(-a)*(((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2*
          ((2:ℝ)^v*(∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ))) =
          ((2:ℝ)^(-a)*(2:ℝ)^v*((2:ℝ)^((v-a)*((d:ℝ)-1)/2))^2)*
            (∫ r, ‖F r‖^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) by ring,
        scalar_angular_shell_normalization]
    _ ≤ H := hH

end Falconer

end OAI
