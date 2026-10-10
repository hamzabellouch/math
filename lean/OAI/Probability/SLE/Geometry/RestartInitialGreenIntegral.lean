import OAI.Probability.SLE.Geometry.RestartGreenIntegral
import OAI.Probability.SLE.Mass.LevelMeanMeasure

namespace OAI

/-! The image of the initial Green measure is the current Green potential.
This is the exact terminal-mean identity for an inverse-Loewner restart. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma initialGreenMeasure_lintegral (κ : ℝ) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : upperHalfPlane, f z ∂initialGreenMeasure κ) =
      ∫⁻ z in upperHalfPlane, f z * ENNReal.ofReal (initialGreen κ z) ∂volume := by
  have hρ : Measurable (fun z => ENNReal.ofReal (initialGreen κ z)) := by
    unfold initialGreen
    fun_prop
  rw [initialGreenMeasure,lintegral_subtype_comap isOpen_upperHalfPlane.measurableSet,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume hρ f
      isOpen_upperHalfPlane.measurableSet (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply lintegral_congr
  intro z
  exact mul_comm _ _

theorem restart_initialGreen_test
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    (κ : ℝ) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : upperHalfPlane, ENNReal.ofReal (‖deriv (F T) ((z:ℂ)+(U T:ℂ))‖^dimension κ) *
      f (F T ((z:ℂ)+(U T:ℂ))) ∂initialGreenMeasure κ) =
      ∫⁻ x in survivingDomain γ T, f x * ENNReal.ofReal (greenDensity κ U γ G T x) := by
  rw [initialGreenMeasure_lintegral κ (fun z : ℂ =>
    ENNReal.ofReal (‖deriv (F T) (z+(U T:ℂ))‖^dimension κ) * f (F T (z+(U T:ℂ))))]
  have he := hw.restart_green_integral hU T hb κ 0 f
  simp only [add_zero] at he
  rw [he]
  apply setLIntegral_congr_fun isOpen_upperHalfPlane.measurableSet
  intro z hz
  dsimp only
  have hUp : Continuous (fun t => U (T+t)-U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [hb.green_initial hUp (by simp) κ hz]
  ac_rfl

end SLEExactGauge.Multipoint

end

end OAI
