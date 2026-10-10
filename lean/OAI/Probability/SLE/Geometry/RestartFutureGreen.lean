import OAI.Probability.SLE.Geometry.RestartHalfPlaneGreen

namespace OAI

/-! The same inverse-map change of variables holds for the Green
remainder at every later time, including tests meeting the old trace. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

theorem restart_future_halfPlane_green_test
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    {κ : ℝ} (hκ : 0 < κ) (t : ℝ≥0) (f : upperHalfPlane → ℝ≥0∞) :
    (∫⁻ z : upperHalfPlane, ENNReal.ofReal (‖deriv (F T) ((z:ℂ)+(U T:ℂ))‖^dimension κ) *
      f (halfPlaneInversePoint hw T z)
        ∂(volume.withDensity (fun z => ENNReal.ofReal
          (greenDensity κ (fun r => U (T+r)-U T) β G' t z))).comap Subtype.val) =
      ∫⁻ x, f x ∂(volume.withDensity (fun x =>
        ENNReal.ofReal (greenDensity κ U γ G (T+t) x))).comap Subtype.val := by
  let e := extendHalfPlaneENN f
  have hUp : Continuous (fun r => U (T+r)-U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [halfPlane_realDensity_lintegral _ (currentGreen_measurable hb hUp hκ t),
    halfPlane_realDensity_lintegral _ (currentGreen_measurable hw hU hκ (T+t))]
  have he := hw.restart_green_integral hU T hb κ t e
  have hs : Function.support (fun z => e z * ENNReal.ofReal
      (greenDensity κ U γ G (T+t) z)) ⊆ survivingDomain γ (T+t) := by
    intro z hz
    by_contra hn
    exact hz (by simp only [greenDensity,ite_eq_right hn,ENNReal.ofReal_zero,mul_zero])
  have hsT := hs.trans (survivingDomain_antitone γ (le_add_right le_rfl))
  rw [setLIntegral_eq_of_support_subset hsT] at he
  rw [setLIntegral_eq_of_support_subset (hs.trans (fun _ hz => hz.1.1))]
  rw [he]
  apply setLIntegral_congr_fun isOpen_upperHalfPlane.measurableSet
  intro z hz
  dsimp only
  rw [show extendHalfPlaneENN (fun w : upperHalfPlane =>
      ENNReal.ofReal (‖deriv (F T) ((w:ℂ)+(U T:ℂ))‖^dimension κ) *
        f (halfPlaneInversePoint hw T w)) z =
      ENNReal.ofReal (‖deriv (F T) (z+(U T:ℂ))‖^dimension κ) *
        e (F T (z+(U T:ℂ))) from by
    rw [extendHalfPlaneENN,dite_eq_left hz]
    change _ = _ * extendHalfPlaneENN f (halfPlaneInversePoint hw T ⟨z,hz⟩)
    rw [extendHalfPlaneENN_apply]]
  ac_rfl

end SLEExactGauge.Multipoint

end

end OAI
