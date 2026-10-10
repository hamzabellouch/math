import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalHeatSample
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatBoxBounds

namespace OAI

/-! Identification and uniform error of the literal rational samples used
in the box quadrature. The required Taylor magnitude follows from the
input radius and the positive time cutoff. -/

namespace ContinuumCoulomb

theorem rationalPosition_eq_pair (q : ℚ × ℚ) :
    PlanarForcingProgram.position q = planarPairEquiv.symm ((q.1 : ℝ), (q.2 : ℝ)) := by
  rw [planarPairEquiv_symm_apply]
  rfl

namespace RationalHeatSample

theorem error_density (x : Input) (ht : 0 < (x.2.1 : ℝ)) (hN : 0 < x.1.2.2)
    (hM : |(exponent x.2 : ℝ)| ≤ x.1.1) :
    |(value x : ℝ) - HeatKernelModulus.density (PlanarForcingProgram.position x.2.2.1)
      (x.2.1 : ℝ) (PlanarForcingProgram.position x.2.2.2)| ≤
      ((2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ)) / (4 * (x.2.1 : ℝ)) := by
  have h := error x ht hN hM
  rw [exact_density] at h
  simpa only [HeatKernelModulus.density, HeatKernelModulus.kernel_eq_heat] using h

theorem error_density_uniform (x : Input) {η : ℝ} (hη : 0 < η) (ht : η ≤ (x.2.1 : ℝ))
    (hN : 0 < x.1.2.2) (hM : |(exponent x.2 : ℝ)| ≤ x.1.1) :
    |(value x : ℝ) - HeatKernelModulus.density (PlanarForcingProgram.position x.2.2.1)
      (x.2.1 : ℝ) (PlanarForcingProgram.position x.2.2.2)| ≤
      ((2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ)) / (4 * η) := by
  apply (error_density x (hη.trans_le ht) hN hM).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

theorem exponent_abs_le (a : Arguments) {η T : ℝ} (hη : 0 < η)
    (ht : η ≤ (a.1 : ℝ)) (hT : (a.1 : ℝ) ≤ T)
    (hy₁ : (a.2.2.1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
    (hy₂ : (a.2.2.2 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) :
    |(exponent a : ℝ)| ≤
      T + (‖PlanarForcingProgram.position a.2.1‖ + 2) ^ 2 / (4 * η) := by
  have ht0 := hη.trans_le ht
  have hd := planarPair_distance_bound (PlanarForcingProgram.position a.2.1)
    (p := ((a.2.2.1 : ℝ), (a.2.2.2 : ℝ))) ⟨hy₁, hy₂⟩
  rw [← rationalPosition_eq_pair] at hd
  have hsq : ‖PlanarForcingProgram.position a.2.1 - PlanarForcingProgram.position a.2.2‖ ^ 2 ≤
      (‖PlanarForcingProgram.position a.2.1‖ + 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  rw [abs_of_nonpos (exponent_nonpos a ht0)]
  have he : (exponent a : ℝ) = -(a.1 : ℝ) -
      ‖PlanarForcingProgram.position a.2.1 - PlanarForcingProgram.position a.2.2‖ ^ 2 /
        (4 * (a.1 : ℝ)) := by
    simp only [exponent, Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_add,
      Rat.cast_pow, Rat.cast_mul, Rat.cast_ofNat, position_sub_norm_sq]
  rw [he]
  have h₁ := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * (a.1 : ℝ) by positivity)
  have h₂ := div_le_div_of_nonneg_left
    (sq_nonneg (‖PlanarForcingProgram.position a.2.1‖ + 2))
    (show 0 < 4 * η by positivity) (show 4 * η ≤ 4 * (a.1 : ℝ) by linarith)
  linarith

end RationalHeatSample
end ContinuumCoulomb

end OAI
