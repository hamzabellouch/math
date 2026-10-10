import OAI.MeasureTheory.Falconer.Incidence.RadialBlockRadius
import OAI.MeasureTheory.Falconer.Geometry.DyadicScaleBallBounds

namespace OAI

/-! # Converting original finite-scale pin hypotheses to local radial costs -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_slab_scale_range {D η : ℝ} (hD : 1 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ)^N)⁻¹ ≤ D*((2:ℝ)^N)^(-η) ∧ D*((2:ℝ)^N)^(-η) ≤ 1 := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη D
  refine ⟨N₀,fun N hN => ?_⟩
  have hR : 0 < (2:ℝ)^N := by positivity
  have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  constructor
  · calc
      _ = ((2:ℝ)^N)^(-(1:ℝ)) := (Real.rpow_neg_one _).symm
      _ ≤ ((2:ℝ)^N)^(-η) := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
      _ ≤ D*((2:ℝ)^N)^(-η) := le_mul_of_one_le_left (by positivity) hD
  · calc
      _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^(-η) :=
        mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
      _ = 1 := by rw [← Real.rpow_add hR]; simp

theorem radial_pin_slab_bound (ν : Measure (Space d)) (N : ℕ)
    {ε ζ D η : ℝ} (hD : 0 ≤ D)
    (hlo : ((2:ℝ)^N)⁻¹ ≤ D*((2:ℝ)^N)^(-η))
    (hhi : D*((2:ℝ)^N)^(-η) ≤ 1)
    (hslab : ∀ w : Space d, ‖w‖ = 1 → ∀ a r : ℝ,
      ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ,
      ν {x | |inner ℝ w x-a| ≤ D*((2:ℝ)^N)^(-η)} ≤
        ENNReal.ofReal (D^ζ*((2:ℝ)^N)^(-(η*ζ-ε))) := by
  intro w hw a
  apply (hslab w hw a _ hlo hhi).trans_eq
  congr 1
  rw [Real.mul_rpow hD (by positivity),← Real.rpow_mul (by positivity)]
  rw [show ((2:ℝ)^N)^ε*(D^ζ*((2:ℝ)^N)^(-η*ζ)) =
    D^ζ*(((2:ℝ)^N)^ε*((2:ℝ)^N)^(-η*ζ)) by ring,
    ← Real.rpow_add (by positivity)]
  congr 2
  ring

end Falconer

end OAI
