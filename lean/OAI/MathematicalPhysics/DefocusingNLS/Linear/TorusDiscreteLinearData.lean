import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDiscreteRadius

namespace OAI

/-! # Uniform stable-graph linear estimates along the expanding orbit -/

open scoped NNReal

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem torusLinearStep_discrete {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (h : HasTorusLinearStep (F := F) T A) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ,
      ∀ L : Radius, L₀ ≤ L.1 →
        ∃ ζ : ℕ → F →L[ℝ] FourierL2, ∃ π : ℕ → FourierL2 →L[ℝ] F,
        ∃ D R : F →L[ℝ] F, (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
          (∀ n v, π n (ζ n v) = v) ∧
          (∀ n, ‖ζ n‖ ≤ 1) ∧ (∀ n, ‖π n‖ ≤ C) ∧
          (∀ n, ‖stableFrameProjection (ζ n) (π n)‖ ≤ C) ∧
          (∀ n, ‖stableProjectedBlock (ζ n) (ζ (n + 1)) (π n) (π (n + 1))
            (A (expandingDiscreteRadius L T n))‖ ≤ 1 / 8) ∧
          (∀ n, ‖stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1))
            (A (expandingDiscreteRadius L T n))‖ ≤ 1 / 16) ∧
          (∀ n, ‖(π (n + 1)).comp (A (expandingDiscreteRadius L T n)) -
            D.comp (π n)‖ ≤ ε) := by
  obtain ⟨C, hC, Lb, ζ, π, D, R, hinv, hR, hframe, hbound, hdefect⟩ := h
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨L₀, hLb, hεL⟩ := hdefect ε hε
  refine ⟨L₀, ?_⟩
  intro L hL
  have hn (n : ℕ) : L₀ ≤ (expandingDiscreteRadius L T n).1 :=
    hL.trans (expandingDiscreteRadius_ge L T n)
  have hb (n : ℕ) := hbound (expandingDiscreteRadius L T n) (hLb.trans (hn n))
  refine ⟨(fun n => ζ (expandingDiscreteRadius L T n)),
    (fun n => π (expandingDiscreteRadius L T n)), D, R, hinv, hR,
    (fun n => hframe _ (hLb.trans (hn n))), (fun n => (hb n).1),
    (fun n => (hb n).2.1), (fun n => (hb n).2.2.1), ?_, ?_, ?_⟩
  · intro n
    simpa only [expandingDiscreteRadius_succ] using (hb n).2.2.2.1
  · intro n
    simpa only [expandingDiscreteRadius_succ] using (hb n).2.2.2.2
  · intro n
    simpa only [expandingDiscreteRadius_succ] using hεL _ (hn n)

end DefocusingNLS

end OAI
