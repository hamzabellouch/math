import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingScalarRetention
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRetainedObservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRunPrefixes
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingTimeCover

namespace OAI

/-! The scalar half-plane detector, built from the full prescribed array.
This is the observation component of the whole-plane fluid theorem. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory
open scoped BigOperators

theorem expanding_scalar_detection (hE : PlaneScalarExistence)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {ν C σ D K : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K) (hcoef : ν * C ≤ σ * 3000)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C) :
    let m := initialWordLength I
    let blank := recorderBlank I.1
    let p := configurationCenter I.1 hI.1 blank m σ D K 0 (finiteInitializedRecorder I hI)
    ∃ w : ℝ → Plane → ℝ,
      GlobalPlaneScalarSolution ν (expandingDrift I.1 hI.1 blank m σ D K) (unitImpulse p) w ∧
      (∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → Integrable (w t)) ∧
      (∀ t, 0 ≤ t → (∫ x, w t x) = smoothRamp 0 1 t) ∧
      ((∃ t : ℝ, 0 ≤ t ∧ 1 / 2 < ∫ x in upperHalfPlane, w t x) ↔ Alternating.Halts I) := by
  dsimp only
  let m := initialWordLength I
  let blank := recorderBlank I.1
  let U₀ := finiteInitializedRecorder I hI
  let p := configurationCenter I.1 hI.1 blank m σ D K 0 U₀
  have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) (le_max_right _ _)
  obtain ⟨w, hw, hwn, hwi, hmass, hret⟩ := expanding_scalar_retention hE I.1 hI.1 blank hm U₀
    (initial_centeredBlank I hI) hσ hD hK hν hC hΔ
  have hwm (t : ℝ) (ht : 0 ≤ t) : (∫ x, w t x) ≤ 1 := unitImpulse_mass_le_one hmass ht
  have ha := expandingDrift_smooth I.1 hI.1 blank m hσ hD hK
  have hdiv := expandingDrift_divergence I.1 hI.1 blank m hσ hD hK
  refine ⟨w, hw, hwn, hwi, hmass, ?_⟩
  constructor
  · rintro ⟨t, ht, hevent⟩
    by_contra hnot
    by_cases ht2 : t ≤ 2
    · have hpflag := recorder_nonhalting_control I hI hnot (Steps.zero U₀)
      have hpbelow : p 1 ≤ -radius σ D K 0 := by
        rw [show p 1 = -(16 * radius σ D K 0) from
          configurationCenter_nonterminal I.1 hI.1 blank m σ D K 0 U₀ hpflag]
        linarith [radius_pos hσ hD hK 0]
      have hcapture := initial_concentration_capture p (hw 2 (by norm_num)) hν.le
        (radius_ge_one hσ hD hK 0) hC ha hdiv hΔ
        (fun s hs => hwi s hs.1) (fun s hs => hwn s hs.1) (fun s hs => hwm s hs.1)
        ht ht2 (fun s hs => funext (fun x =>
          expandingDrift_initial I.1 hI.1 blank m hσ hD hK (hs.2.le.trans ht2) x))
      have hr : (∫ x, w t x) - ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * t ≤
          ∫ x, concentrationCutoff (radius σ D K 0) p x * w t x := by
        rw [hmass t ht]
        exact hcapture
      have hb := concentration_nonterminal_observer (hwi t ht) (hwn t ht)
        (radius_pos hσ hD hK 0) hpbelow hr
      have hsmall := (initialLoss_partial_le hν.le hC ht2).trans_lt
        (accumulatedLoss_lt hσ hD hK hcoef 0)
      linarith
    · obtain ⟨n, hnt, htn⟩ := exists_stage_at_time hσ hD hK (le_of_lt (lt_of_not_ge ht2))
      obtain ⟨V, hrun, hV⟩ := nonhalting_recorder_prefix I hI hnot (n + 1)
      cases hrun with
      | @next n U₀ U V hprefix hstep =>
        let W : StageWire I.1 hI.1 blank (m + n) :=
          ⟨(configurationAddress I.1 blank (m + n) U,
            configurationAddress I.1 blank (m + n + 1) V),
            configurationAddress_step I.1 hI.1 blank (by omega)
              (initialized_steps_centeredBlank I hI hprefix) hstep⟩
        let c := wireCurve I.1 hI.1 blank (m + n) (stageStart σ D K n) (duration σ D K n)
          (radius σ D K n) (radius σ D K (n + 1)) W
        have hs := recorder_stage_partial_retention I.1 hI.1 blank hm hσ hD hK hν.le hC p
          hw hwi hwn hwm hΔ (initialized_steps_centeredBlank I hI hprefix) hstep hnt htn.le
        have hr0 := hret n U hprefix
        have hbudget := accumulatedLoss_partial_le hν.le hC n htn.le
        have hmass1 := unitImpulse_mass_after hmass (by linarith : 1 ≤ t)
        have hr : (∫ x, w t x) - accumulatedLoss ν C σ D K (n + 1) ≤
            ∫ x, concentrationCutoff (radius σ D K n) (c t) x * w t x := by
          change _ ≤ ∫ x, concentrationCutoff (radius σ D K n) (c t) x * w t x at hs
          rw [hmass1]
          dsimp only [accumulatedLoss] at hbudget ⊢
          linarith
        have hcbelow : c t 1 ≤ -radius σ D K n := by
          have hT : 0 < duration σ D K n :=
            lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hσ hD hK n)
          have hR := radius_pos hσ hD hK n
          have hRR := radius_grows hσ hD hK n
          have hcn : c t 1 ≤ -(16 * radius σ D K n) := by
            change scheduledCenter _ _ _ _ _ _ (haltingControl (finiteMachine I.1 hI.1) V.control) t 1 ≤ _
            rw [hV]
            exact scheduledCenter_nonterminal _ hT (by positivity) (by linarith) _ _ t
          linarith
        have hb := concentration_nonterminal_observer (hwi t ht) (hwn t ht)
          (radius_pos hσ hD hK n) hcbelow hr
        linarith [accumulatedLoss_lt hσ hD hK hcoef (n + 1)]
  · intro hhalt
    obtain ⟨n, U, q, hrun, hq, hh⟩ := (finite_recorder_halts_iff I hI).mpr hhalt
    have ht2 : 2 ≤ stageStart σ D K n := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [stageStart_ge hσ hD hK n]
    have ht := le_trans (by norm_num : (0 : ℝ) ≤ 2) ht2
    have hflag : haltingControl (finiteMachine I.1 hI.1) U.control = true := by
      rw [hq]
      exact hh
    have hr : 1 - accumulatedLoss ν C σ D K n ≤
        ∫ x, concentrationCutoff (radius σ D K n)
          (configurationCenter I.1 hI.1 blank m σ D K n U) x * w (stageStart σ D K n) x := by
      have hh := hret n U hrun
      dsimp only [accumulatedLoss]
      linarith
    exact ⟨stageStart σ D K n, ht,
      retained_terminal_observation I.1 hI.1 blank m hσ hD hK hcoef n U hflag
        (hwi _ ht) (hwn _ ht) (unitImpulse_mass_after hmass (by linarith)) hr⟩

end ForcedComputation.ExpandingDetector

end

end OAI
