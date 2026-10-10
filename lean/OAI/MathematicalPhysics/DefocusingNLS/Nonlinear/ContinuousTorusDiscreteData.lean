import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusLinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDiscreteRadius

namespace OAI

/-! # Continuous linear data along the expanding discrete orbit -/

open scoped NNReal

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem continuous_expandingDiscreteRadius (T : ℝ≥0) (n : ℕ) :
    Continuous (fun L : Radius => expandingDiscreteRadius L T n) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.mul continuous_const

theorem continuous_torusLinearStep_discrete {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (h : HasContinuousTorusLinearStep (F := F) T A) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ,
      ∃ ζ : Radius → ℕ → F →L[ℝ] FourierL2,
      ∃ π : Radius → ℕ → FourierL2 →L[ℝ] F,
      ∃ D R : F →L[ℝ] F, (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
        (∀ n, ContinuousOn (fun L => ζ L n) {L : Radius | L₀ ≤ L.1}) ∧
        (∀ n, Continuous (fun p : Radius × FourierL2 => π p.1 n p.2)) ∧
        ∀ L : Radius, L₀ ≤ L.1 →
          (∀ n v, π L n (ζ L n v) = v) ∧
          (∀ n, ‖ζ L n‖ ≤ 1) ∧ (∀ n, ‖π L n‖ ≤ C) ∧
          (∀ n, ‖stableFrameProjection (ζ L n) (π L n)‖ ≤ C) ∧
          (∀ n, ‖stableProjectedBlock (ζ L n) (ζ L (n + 1)) (π L n) (π L (n + 1))
            (A (expandingDiscreteRadius L T n))‖ ≤ 1 / 8) ∧
          (∀ n, ‖stableMixedBlock (ζ L n) (ζ L (n + 1)) (π L (n + 1))
            (A (expandingDiscreteRadius L T n))‖ ≤ 1 / 16) ∧
          (∀ n, ‖(π L (n + 1)).comp (A (expandingDiscreteRadius L T n)) -
            D.comp (π L n)‖ ≤ ε) := by
  obtain ⟨C, hC, Lb, ζ, π, D, R, hinv, hR, hframe, hbound, hdefect, hζc, hπc⟩ := h
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨L₀, hLb, hεL⟩ := hdefect ε hε
  refine ⟨L₀, (fun L n => ζ (expandingDiscreteRadius L T n)),
    (fun L n => π (expandingDiscreteRadius L T n)), D, R, hinv, hR, ?_, ?_, ?_⟩
  · intro n
    exact hζc.comp (continuous_expandingDiscreteRadius T n).continuousOn
      (fun L hL => hLb.trans (hL.trans (expandingDiscreteRadius_ge L T n)))
  · intro n
    exact hπc.comp (((continuous_expandingDiscreteRadius T n).comp continuous_fst).prodMk
      continuous_snd)
  · intro L hL
    have hn (n : ℕ) : L₀ ≤ (expandingDiscreteRadius L T n).1 :=
      hL.trans (expandingDiscreteRadius_ge L T n)
    have hb (n : ℕ) := hbound (expandingDiscreteRadius L T n) (hLb.trans (hn n))
    refine ⟨(fun n => hframe _ (hLb.trans (hn n))), (fun n => (hb n).1),
      (fun n => (hb n).2.1), (fun n => (hb n).2.2.1), ?_, ?_, ?_⟩
    · intro n
      simpa only [expandingDiscreteRadius_succ] using (hb n).2.2.2.1
    · intro n
      simpa only [expandingDiscreteRadius_succ] using (hb n).2.2.2.2
    · intro n
      simpa only [expandingDiscreteRadius_succ] using hεL _ (hn n)

end DefocusingNLS

end OAI
