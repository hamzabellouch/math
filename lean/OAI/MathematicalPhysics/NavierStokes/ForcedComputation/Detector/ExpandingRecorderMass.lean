import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneImpulseScalar
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDriftStage
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMassEvolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderSupport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCutoffObservation

namespace OAI

/-! Mass transport along an actual recorder instruction.  The prescribed
field still contains every finite address edge; only the test follows the
selected execution. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory

 def configurationCenter (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℝ) (n : ℕ) (U : Configuration (State M) (Alphabet M)) : Plane :=
  ![16 * radius σ D K n * (configurationAddress M blank (m + n) U).number,
    if haltingControl (finiteMachine M hM) U.control then
      16 * radius σ D K n else -(16 * radius σ D K n)]

theorem recorder_step_mass_retention
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {m : ℕ} (hm : 0 < m)
    {σ D K ν C : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (p : Plane)
    {w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν (expandingDrift M hM blank m σ D K) (unitImpulse p) w)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t))
    (hwn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x)
    (hwm : ∀ t, 0 ≤ t → (∫ x, w t x) ≤ 1)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C)
    {n : ℕ} {U V : Configuration (State M) (Alphabet M)}
    (hU : CenteredBlank blank (m + n) U) (hstep : Step (finiteMachine M hM) U V) :
    (∫ x, concentrationCutoff (radius σ D K n)
      (configurationCenter M hM blank m σ D K n U) x * w (stageStart σ D K n) x) -
        ν * ((radius σ D K n)⁻¹ ^ 2 * C) * duration σ D K n ≤
    ∫ x, concentrationCutoff (radius σ D K (n + 1))
      (configurationCenter M hM blank m σ D K (n + 1) V) x * w (stageStart σ D K (n + 1)) x := by
  let W : StageWire M hM blank (m + n) :=
    ⟨(configurationAddress M blank (m + n) U,
       configurationAddress M blank (m + n + 1) V),
      configurationAddress_step M hM blank (by omega) hU hstep⟩
  let c := wireCurve M hM blank (m + n) (stageStart σ D K n)
    (duration σ D K n) (radius σ D K n) (radius σ D K (n + 1)) W
  have hT : 0 < duration σ D K n :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hσ hD hK n)
  have ht0 : 0 ≤ stageStart σ D K n := by linarith [stageStart_ge hσ hD hK n]
  have htt : stageStart σ D K n ≤ stageStart σ D K (n + 1) :=
    (stageStart_strictMono hσ hD hK).monotone (by omega)
  have ht1 := ht0.trans htt
  obtain ⟨B, _, hB⟩ := scheduledCenter_bounded (stageStart σ D K n) hT
    (16 * radius σ D K n) (16 * radius σ D K (n + 1))
    W.val.1.number W.val.2.number (haltingControl (finiteMachine M hM) W.val.2.control)
  have hret := concentration_mass_retention (hw _ ht1) hν (radius_pos hσ hD hK n) hC
    (expandingDrift_smooth M hM blank m hσ hD hK) (unitImpulse_smooth p)
    (expandingDrift_divergence M hM blank m hσ hD hK)
    (wireCurve_smooth M hM blank (m + n) _ _ _ _ W) ⟨B, hB⟩ hΔ
    (fun t ht => hwi t ht.1) (fun t ht => hwn t ht.1) (fun t ht => hwm t ht.1)
    (fun t _ x => unitImpulse_nonneg p t x) ht0 htt le_rfl
    (fun t ht x hx => expandingDrift_rigid M hM blank m hσ hD hK n W
      ht.1.le ht.2.le x hx)
  have hnon : haltingControl (finiteMachine M hM) U.control = false := by
    obtain ⟨_, _, _, hs, _⟩ := hstep
    exact hs.source_nonhalting
  have hc0 : c (stageStart σ D K n) = configurationCenter M hM blank m σ D K n U := by
    rw [show c (stageStart σ D K n) = _ from scheduledCenter_initial _ hT _ _ _ _ _]
    simp only [configurationCenter, hnon, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hc1 : c (stageStart σ D K (n + 1)) =
      configurationCenter M hM blank m σ D K (n + 1) V := by
    rw [stageStart_succ]
    rw [show c (stageStart σ D K n + duration σ D K n) = _ from
      scheduledCenter_final _ hT _ _ _ _ _]
    simp only [configurationCenter]
    rfl
  change (∫ x, concentrationCutoff (radius σ D K n) (c (stageStart σ D K n)) x *
    w (stageStart σ D K n) x) - _ ≤
    ∫ x, concentrationCutoff (radius σ D K n) (c (stageStart σ D K (n + 1))) x *
      w (stageStart σ D K (n + 1)) x at hret
  have htime : stageStart σ D K (n + 1) - stageStart σ D K n = duration σ D K n := by
    rw [stageStart_succ, add_sub_cancel_left]
  rw [hc0, hc1, htime, mul_one] at hret
  exact hret.trans (concentration_mass_le_doubled (hwi _ ht1) (hwn _ ht1)
    (radius_pos hσ hD hK n) (radius_grows hσ hD hK n) _)

theorem recorder_stage_partial_retention
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {m : ℕ} (hm : 0 < m)
    {σ D K ν C : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (p : Plane)
    {w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν (expandingDrift M hM blank m σ D K) (unitImpulse p) w)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t))
    (hwn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x)
    (hwm : ∀ t, 0 ≤ t → (∫ x, w t x) ≤ 1)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C)
    {n : ℕ} {U V : Configuration (State M) (Alphabet M)}
    (hU : CenteredBlank blank (m + n) U) (hstep : Step (finiteMachine M hM) U V)
    {b : ℝ} (hb : stageStart σ D K n ≤ b) (hb' : b ≤ stageStart σ D K (n + 1)) :
    (∫ x, concentrationCutoff (radius σ D K n)
      (configurationCenter M hM blank m σ D K n U) x * w (stageStart σ D K n) x) -
        ν * ((radius σ D K n)⁻¹ ^ 2 * C) * (b - stageStart σ D K n) ≤
    ∫ x, concentrationCutoff (radius σ D K n)
      (wireCurve M hM blank (m + n) (stageStart σ D K n) (duration σ D K n)
        (radius σ D K n) (radius σ D K (n + 1))
        ⟨(configurationAddress M blank (m + n) U,
          configurationAddress M blank (m + n + 1) V),
          configurationAddress_step M hM blank (by omega) hU hstep⟩ b) x * w b x := by
  let W : StageWire M hM blank (m + n) :=
    ⟨(configurationAddress M blank (m + n) U,
       configurationAddress M blank (m + n + 1) V),
      configurationAddress_step M hM blank (by omega) hU hstep⟩
  let c := wireCurve M hM blank (m + n) (stageStart σ D K n)
    (duration σ D K n) (radius σ D K n) (radius σ D K (n + 1)) W
  have hT : 0 < duration σ D K n :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hσ hD hK n)
  have ht0 : 0 ≤ stageStart σ D K n := by linarith [stageStart_ge hσ hD hK n]
  have ht1 := ht0.trans hb
  obtain ⟨B, _, hB⟩ := scheduledCenter_bounded (stageStart σ D K n) hT
    (16 * radius σ D K n) (16 * radius σ D K (n + 1))
    W.val.1.number W.val.2.number (haltingControl (finiteMachine M hM) W.val.2.control)
  have hret := concentration_mass_retention (hw _ ht1) hν (radius_pos hσ hD hK n) hC
    (expandingDrift_smooth M hM blank m hσ hD hK) (unitImpulse_smooth p)
    (expandingDrift_divergence M hM blank m hσ hD hK)
    (wireCurve_smooth M hM blank (m + n) _ _ _ _ W) ⟨B, hB⟩ hΔ
    (fun t ht => hwi t ht.1) (fun t ht => hwn t ht.1) (fun t ht => hwm t ht.1)
    (fun t _ x => unitImpulse_nonneg p t x) ht0 hb le_rfl
    (fun t ht x hx => expandingDrift_rigid M hM blank m hσ hD hK n W
      ht.1.le (ht.2.le.trans hb') x hx)
  have hnon : haltingControl (finiteMachine M hM) U.control = false := by
    obtain ⟨_, _, _, hs, _⟩ := hstep
    exact hs.source_nonhalting
  have hc0 : c (stageStart σ D K n) = configurationCenter M hM blank m σ D K n U := by
    rw [show c (stageStart σ D K n) = _ from scheduledCenter_initial _ hT _ _ _ _ _]
    simp only [configurationCenter, hnon, Bool.false_eq_true, ↓reduceIte]
    rfl
  change (∫ x, concentrationCutoff (radius σ D K n) (c (stageStart σ D K n)) x *
    w (stageStart σ D K n) x) - _ ≤
    ∫ x, concentrationCutoff (radius σ D K n) (c b) x * w b x at hret
  rw [hc0, mul_one] at hret
  exact hret

end ForcedComputation.ExpandingDetector

end

end OAI
