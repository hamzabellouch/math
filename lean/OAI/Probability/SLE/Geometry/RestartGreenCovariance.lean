import OAI.Probability.SLE.Mass.RestartMassCoordinates

namespace OAI

/-! Exact survival and Green-density covariance under the actual restart
map. The area Jacobian changes the Green exponent into the mass exponent. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

lemma IsCapacityTwoWitness.restart_surviving_iff
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    F T (z+(U T:ℂ)) ∈ survivingDomain γ (T+t) ↔ z ∈ survivingDomain β t := by
  refine ⟨?_,fun h => (hw.restart_forward_composition T hb t z h).1⟩
  intro hy
  let y := F T (z+(U T:ℂ))
  let v := G (T+t) y-(U T:ℂ)
  have hv : v ∈ upperHalfPlane := by
    simpa only [v,upperHalfPlane,mem_ofPred_eq,Complex.sub_im,Complex.ofReal_im,sub_zero]
      using hw.2.2.2.2.2.1 (T+t) hy
  have hfv := hb.2.2.2.2.2.2.1 t hv
  have hi : F T (F' t v+(U T:ℂ)) = F T (z+(U T:ℂ)) := by
    rw [← hw.restart_inverse_composition T hb t v hv]
    change F (T+t) ((G (T+t) y-(U T:ℂ))+(U T:ℂ)) = y
    rw [sub_add_cancel,hw.2.2.2.2.2.2.2.1 (T+t) y hy]
  have hfH : F' t v+(U T:ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
      using hfv.1.1
  have hzH : z+(U T:ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero] using hz
  have hh := congrArg (G T) hi
  rw [hw.2.2.2.2.2.2.2.2.1 T _ hfH,hw.2.2.2.2.2.2.2.2.1 T _ hzH] at hh
  have he : F' t v = z := add_right_cancel hh
  rwa [he] at hfv

lemma IsCapacityTwoWitness.restart_green_covariance_alive
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    (κ : ℝ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain β t) :
    greenDensity κ U γ G (T+t) (F T (z+(U T:ℂ))) =
      ‖deriv (F T) (z+(U T:ℂ))‖ ^ (-codimension κ) *
        greenDensity κ (fun r => U (T+r)-U T) β G' t z := by
  have hy := (hw.restart_forward_composition T hb t z hz).1
  have hUp : Continuous (fun r => U (T+r)-U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [greenDensity,ite_eq_left hy,greenDensity,ite_eq_left hz,
    hw.restart_radius_composition hU T hb t z hz,hw.restart_centered_value T hb t z hz,
    Real.mul_rpow (norm_nonneg _) (hb.fullRadius_positive hUp t z hz).le]
  ring

theorem IsCapacityTwoWitness.restart_green_area_covariance
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    (κ : ℝ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    ‖deriv (F T) (z+(U T:ℂ))‖^2 *
        greenDensity κ U γ G (T+t) (F T (z+(U T:ℂ))) =
      ‖deriv (F T) (z+(U T:ℂ))‖^(dimension κ) *
        greenDensity κ (fun r => U (T+r)-U T) β G' t z := by
  by_cases halive : z ∈ survivingDomain β t
  · have hy := (hw.restart_forward_composition T hb t z halive).1
    have hUp : Continuous (fun r => U (T+r)-U T) :=
      (hU.comp (continuous_const.add continuous_id)).sub continuous_const
    have hr := hw.restart_radius_composition hU T hb t z halive
    have hR := hw.fullRadius_positive hU (T+t) _ hy
    have hR' := hb.fullRadius_positive hUp t z halive
    have hd : 0 < ‖deriv (F T) (z+(U T:ℂ))‖ := by
      rw [hr] at hR
      nlinarith [norm_nonneg (deriv (F T) (z+(U T:ℂ)))]
    have hp : ‖deriv (F T) (z+(U T:ℂ))‖^2 *
        ‖deriv (F T) (z+(U T:ℂ))‖^(-codimension κ) =
        ‖deriv (F T) (z+(U T:ℂ))‖^(dimension κ) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hd]
      congr 1
      simp only [codimension,Nat.cast_ofNat]
      ring
    rw [hw.restart_green_covariance_alive hU T hb κ t z halive,← mul_assoc,hp]
  · have hy : F T (z+(U T:ℂ)) ∉ survivingDomain γ (T+t) :=
      fun h => halive ((hw.restart_surviving_iff T hb t z hz).mp h)
    simp only [greenDensity,ite_eq_right hy,ite_eq_right halive,mul_zero]

end SLEExactGauge

end

end OAI
