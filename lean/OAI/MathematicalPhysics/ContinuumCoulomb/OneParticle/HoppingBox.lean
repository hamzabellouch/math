import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolventModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatBoxCoordinates
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatSampleError

namespace OAI

/-! The actual contact numerator is an integral over the fixed forcing
square. Its translated sample point is represented exactly by rational
subtraction, so the concrete resolvent evaluator applies directly. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarHoppingNumerator (d : ℝ) : ℝ := ∫ r, planarHoppingIntegrand d r

theorem planarHopping_eq_numerator (d : ℝ) :
    planarHopping d = planarHoppingNumerator d / (2 * ∫ r, planarResolventMode r ^ 2) := rfl

theorem planarHoppingNumerator_box (d : ℝ) :
    planarHoppingNumerator d = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      planarHoppingIntegrand d (planarPairEquiv.symm (x, y)) := by
  unfold planarHoppingNumerator
  rw [planarPair_integral]
  let f := fun p : ℝ × ℝ => planarHoppingIntegrand d (planarPairEquiv.symm p)
  have hf : Continuous f := (planarHoppingIntegrand_continuous d).comp planarPairEquiv_symm_continuous
  have hi : IntegrableOn f (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs : (∫ p, f p) = ∫ p in Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1, f p := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [f, planarHoppingIntegrand, planarForcing_pair_zero hp, zero_mul]
  change (∫ p, f p) = _
  rw [hs, Measure.volume_eq_prod, setIntegral_prod f hi]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rfl

theorem rationalPosition_shift_first (d a b : ℚ) :
    PlanarForcingProgram.position (a - d, b) =
      PlanarForcingProgram.position (a, b) - (d : ℝ) • planarAxis 0 := by
  ext i
  fin_cases i <;> simp [PlanarForcingProgram.position, planarAxis]

theorem rationalShift_norm_bound (d a b : ℚ) {R : ℝ}
    (hd : |(d : ℝ)| ≤ R)
    (ha : (a : ℝ) ∈ Set.Icc (-1 : ℝ) 1) (hb : (b : ℝ) ∈ Set.Icc (-1 : ℝ) 1) :
    ‖PlanarForcingProgram.position (a - d, b)‖ ≤ R + 2 := by
  rw [rationalPosition_shift_first]
  have hnorm : ‖PlanarForcingProgram.position (a, b)‖ ≤ 2 := by
    rw [rationalPosition_eq_pair]
    exact planarPair_norm_le_two ⟨ha, hb⟩
  have ht : ‖(d : ℝ) • planarAxis 0‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, planarAxis_zero_norm, mul_one]
    exact hd
  exact (norm_sub_le _ _).trans (by linarith)

end ContinuumCoulomb

end

end OAI
