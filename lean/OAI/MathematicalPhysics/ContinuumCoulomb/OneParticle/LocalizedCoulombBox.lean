import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombTruncation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombNumerics
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedDensityMoment

namespace OAI

/-! The actual direct coefficient is approximated by a bounded integral
on a six-dimensional rational cube. The cap and truncation errors are
uniform in the relative displacement of the two fixed density packets. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def coulombNumericalBox (L : ℝ) : Set Position :=
  ⋂ i : Fin 3, {x : Position | |x i| ≤ L}

theorem coulombNumericalBox_measurable (L : ℝ) : MeasurableSet (coulombNumericalBox L) := by
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem coulombNumericalBox_outside (L : ℝ) {x : Position}
    (hx : x ∉ coulombNumericalBox L) : L ≤ ‖x‖ := by
  simp only [coulombNumericalBox, Set.mem_iInter, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  exact (lt_of_not_ge hi).le.trans (by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)

def localizedCappedProfile (freq ε : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ p, cappedPairIntegrand ε (planarCenter u)
    (localizedDensity freq 0) (localizedDensity freq 0) p

theorem localizedCappedProfile_eq {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u : PlanarPosition) :
    localizedCappedProfile freq ε u = localizedCappedCoulombCoeff freq ε 0 u := by
  rw [localizedCappedCoulombCoeff_nested hfreq hε]
  unfold localizedCappedProfile
  rw [Measure.volume_eq_prod, integral_prod _ (by
    simpa only [Measure.volume_eq_prod] using cappedPairIntegrand_integrable hε
      (planarCenter u) (localizedDensity_integrable hfreq 0)
      (localizedDensity_integrable hfreq 0))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [cappedPairIntegrand, cappedCoulombPotential]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  congr 1
  rw [← integral_add_right_eq_self
    (fun y => cappedCoulombKernel ε (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_translate freq u, add_sub_cancel_right]
  rw [mul_comm]
  congr 1
  abel_nf

def localizedCoulombBoxIntegral (freq ε L : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ p in coulombNumericalBox L ×ˢ coulombNumericalBox L,
    cappedPairIntegrand ε (planarCenter u)
      (localizedDensity freq 0) (localizedDensity freq 0) p

theorem localizedCappedProfile_box_error {freq ε L : ℝ}
    (hfreq : 0 < freq) (hε : 0 < ε) (hL : 0 < L) (u : PlanarPosition) :
    |localizedCappedProfile freq ε u - localizedCoulombBoxIntegral freq ε L u| ≤
      2 * ε⁻¹ * localizedDensitySecondMoment freq / L ^ 2 := by
  have ht := cappedPair_truncation_error hε (planarCenter u)
    (localizedDensity_integrable hfreq 0) (localizedDensity_integrable hfreq 0)
    (localizedDensity_nonnegative freq 0) (localizedDensity_nonnegative freq 0)
    (coulombNumericalBox_measurable L) (coulombNumericalBox_measurable L)
  simp only [localizedDensity_mass hfreq 0, mul_one, one_mul] at ht
  have hb := localizedDensity_tail_of_norm hfreq hL (coulombNumericalBox_measurable L)
    (fun _ hx => coulombNumericalBox_outside L hx)
  apply ht.trans
  have hε0 : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  calc
    _ ≤ ε⁻¹ * (localizedDensitySecondMoment freq / L ^ 2 +
        localizedDensitySecondMoment freq / L ^ 2) := by gcongr
    _ = _ := by ring

theorem localizedCoulombProfile_box_error {freq ε L : ℝ}
    (hfreq : 0 < freq) (hε : 0 < ε) (hL : 0 < L) (u : PlanarPosition) :
    |localizedCoulombProfileAt freq u - localizedCoulombBoxIntegral freq ε L u| ≤
      2 * Real.pi * localizedAmplitudeBound freq ^ 2 * ε ^ 2 +
        2 * ε⁻¹ * localizedDensitySecondMoment freq / L ^ 2 := by
  have hcap := localizedCappedCoulombCoeff_error hfreq hε 0 u
  rw [← localizedCoulombProfileAt_eq, ← localizedCappedProfile_eq hfreq hε] at hcap
  exact (abs_sub_le _ (localizedCappedProfile freq ε u) _).trans
    (add_le_add hcap (localizedCappedProfile_box_error hfreq hε hL u))

end ContinuumCoulomb

end

end OAI
