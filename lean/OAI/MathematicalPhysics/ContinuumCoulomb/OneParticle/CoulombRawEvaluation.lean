import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombEvaluationParameters

namespace OAI

/-! The fixed polynomial schedule approximates the actual unnormalized
Coulomb box integral uniformly in every rational separation. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation
open UniformQuadrature

theorem position_shift (d : ℚ) :
    CappedKernelProgram.position (d, 0, 0) = planarCenter ((d : ℝ) • planarAxis 0) := by
  apply positionSplitCoordinates.injective
  rw [RawDensitySample.position_split]
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [PlanarForcingProgram.position, planarAxis]
  · simp

theorem denominator_inverse (rho P : ℕ) :
    (1 / (denominator rho P : ℚ) : ℝ)⁻¹ = (denominator rho P : ℝ) := by
  simp only [Rat.cast_natCast, one_div, inv_inv]

theorem rational_box_quadrature_error (rho R Q b N D : ℕ) (hD : 0 < D) (hN : 0 < N) (d : ℚ)
    (hf : 0 < GaussianFrequency.frequency rho) :
    |(RationalSixQuadrature.value (RawCoulombSample.sixEvaluator rho)
        (RawCoulombSample.quadratureInput R Q b (1 / (D : ℚ)) (d, 0, 0) N) : ℝ) -
      localizedRawCoulombBox (GaussianFrequency.frequency rho) (1 / (D : ℝ)) R
        ((d : ℝ) • planarAxis 0)| ≤
      (2 * (R : ℝ)) ^ 6 *
        (6 * ((64 + 2 * GaussianFrequency.frequency rho * R) * D + (D : ℝ) ^ 2) *
          (2 * (R : ℝ) / N) +
          (8 * D * ((Q : ℝ) + 1)⁻¹ + (D : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ b)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hε : (0 : ℚ) < 1 / (D : ℚ) := by positivity
  have hεr : (0 : ℝ) < 1 / (D : ℝ) := by positivity
  have hq := RawCoulombSample.quadrature_error rho R Q b N hε hN (d, 0, 0)
  have hbox := localizedRawCoulombBox_cube hf hεr (Nat.cast_nonneg R) ((d : ℝ) • planarAxis 0)
  rw [← position_shift] at hbox
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hq
  have hbox' : cubeIntegral (-(R : ℝ)) (R : ℝ) 6
      (rawCoulombSix (GaussianFrequency.frequency rho) (1 / (D : ℝ))
        (CappedKernelProgram.position (d, 0, 0))) =
      localizedRawCoulombBox (GaussianFrequency.frequency rho) (1 / (D : ℝ))
        (R : ℝ) ((d : ℝ) • planarAxis 0) := hbox.symm
  rw [hbox'] at hq
  simpa only [one_div, inv_inv] using hq

theorem natural_quadrature_budget (F R D S : ℕ) {f : ℝ}
    (hRnat : 0 < R) (hDnat : 0 < D) (hSnat : 0 < S) (hf : f ≤ F) :
    (2 * (R : ℝ)) ^ 6 *
        (6 * ((64 + 2 * f * R) * D + (D : ℝ) ^ 2) *
          (2 * (R : ℝ) / CoulombQuadratureSchedule.mesh F R D S) +
          (8 * D * ((CoulombQuadratureSchedule.accuracy R D S : ℝ) + 1)⁻¹ +
            (D : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ CoulombQuadratureSchedule.kernelPrecision R D S)) ≤
      3 * (4 * (S : ℝ))⁻¹ := by
  let L := CoulombQuadratureSchedule.lipschitz F R D
  let V := CoulombQuadratureSchedule.volume R
  have hR : (0 : ℝ) < R := by exact_mod_cast hRnat
  have hD : (0 : ℝ) < D := by exact_mod_cast hDnat
  have hS : (0 : ℝ) < S := by exact_mod_cast hSnat
  have hV : (V : ℝ) = (2 * (R : ℝ)) ^ 6 := by
    simp only [V, CoulombQuadratureSchedule.volume, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  have hL : (L : ℝ) = (64 + 2 * (F : ℝ) * R) * D + (D : ℝ) ^ 2 := by
    simp only [L, CoulombQuadratureSchedule.lipschitz, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
  have hL0 : (0 : ℝ) < L := by rw [hL]; positivity
  have hN : (CoulombQuadratureSchedule.mesh F R D S : ℝ) = 48 * R * L * V * S := by
    simp only [CoulombQuadratureSchedule.mesh, Nat.cast_mul, Nat.cast_ofNat, L, V]
  have hQ : (CoulombQuadratureSchedule.accuracy R D S : ℝ) = 32 * D * V * S := by
    simp only [CoulombQuadratureSchedule.accuracy, Nat.cast_mul, Nat.cast_ofNat, V]
  have hb : (CoulombQuadratureSchedule.kernelPrecision R D S : ℝ) = 4 * (D : ℝ) ^ 2 * V * S := by
    simp only [CoulombQuadratureSchedule.kernelPrecision,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, V]
  have hLip : (64 + 2 * f * R) * D + (D : ℝ) ^ 2 ≤ L := by
    rw [hL]
    gcongr
  have hupper := CoulombQuadratureSchedule.scalar_budget hR hD hL0 hS hV hN hQ hb
  apply le_trans _ hupper
  rw [hV]
  simp only [add_assoc]
  gcongr

theorem raw_approximation_error (rho P : ℕ) (hrho : 0 < rho) (d : ℚ) :
    |(rawApproximate rho P d : ℝ) -
      localizedRawCoulombBox (GaussianFrequency.frequency rho)
        (1 / (denominator rho P : ℚ) : ℝ) (radius rho P : ℝ) ((d : ℝ) • planarAxis 0)| ≤
      3 * (4 * (rawPrecision rho P : ℝ))⁻¹ := by
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hq := rational_box_quadrature_error rho (radius rho P) (samplePrecision rho P)
    (kernelPrecision rho P) (mesh rho P) (denominator rho P) (denominator_positive rho P)
      (mesh_positive rho P) d hf
  have hb := natural_quadrature_budget (frequencyBound rho) (radius rho P)
    (denominator rho P) (rawPrecision rho P) (radius_positive rho P)
      (denominator_positive rho P) (rawPrecision_positive rho P) (frequencyBound_le rho)
  have hc := hq.trans hb
  simpa only [rawApproximate, input, Rat.cast_natCast] using hc

end ContinuumCoulomb.CoulombEvaluation

end

end OAI
