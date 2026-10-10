import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusDiscreteData
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusLinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusFrameNormalization

namespace OAI

/-! # Continuous linear data retaining the original torus coordinate map -/

open scoped NNReal

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def HasContinuousTorusCoordinateData (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (κ : Radius → FourierL2 →L[ℝ] F) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∃ ζ : Radius → F →L[ℝ] FourierL2,
    let π := fun L => K • κ L
    ∃ D R : F →L[ℝ] F, (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
      (∀ L : Radius, L₀ ≤ L.1 → ∀ v, π L (ζ L v) = v) ∧
      (∀ L : Radius, L₀ ≤ L.1 →
        ‖ζ L‖ ≤ 1 ∧ ‖π L‖ ≤ C ∧ ‖stableFrameProjection (ζ L) (π L)‖ ≤ C ∧
        ‖stableProjectedBlock (ζ L) (ζ (torusEndpointRadius T L))
          (π L) (π (torusEndpointRadius T L)) (A L)‖ ≤ 1 / 8 ∧
        ‖stableMixedBlock (ζ L) (ζ (torusEndpointRadius T L))
          (π (torusEndpointRadius T L)) (A L)‖ ≤ 1 / 16) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Lε : ℝ, L₀ ≤ Lε ∧ ∀ L : Radius, Lε ≤ L.1 →
        ‖(π (torusEndpointRadius T L)).comp (A L) - D.comp (π L)‖ ≤ ε) ∧
      ContinuousOn ζ {L : Radius | L₀ ≤ L.1} ∧
      Continuous (fun p : Radius × FourierL2 => π p.1 p.2)

theorem continuous_torusCoordinateData_of_frames (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (ζ : Radius → F →L[ℝ] FourierL2) (π : Radius → FourierL2 →L[ℝ] F)
    (D R : F →L[ℝ] F) (hinv : ∀ v, D (R v) = v) (hR : ‖R‖ ≤ 1)
    (L₀ C Cπ CA : ℝ) (hC : 0 ≤ C) (hCπ : 0 ≤ Cπ) (hCA : 0 ≤ CA)
    (hframe : ∀ L : Radius, L₀ ≤ L.1 →
      (∀ v, π L (ζ L v) = v) ∧ ‖ζ L‖ ≤ C ∧ ‖π L‖ ≤ Cπ ∧
      ‖stableFrameProjection (ζ L) (π L)‖ ≤ C)
    (hstable : ∀ L : Radius, L₀ ≤ L.1 →
      ‖stableProjectedBlock (ζ L) (ζ (torusEndpointRadius T L))
        (π L) (π (torusEndpointRadius T L)) (A L)‖ ≤ 1 / 8)
    (hA : ∀ L : Radius, ‖A L‖ ≤ CA)
    (hdefect : ∀ ε : ℝ, 0 < ε → ∃ Lε : ℝ, ∀ L : Radius, Lε ≤ L.1 →
      ‖(π (torusEndpointRadius T L)).comp (A L) - D.comp (π L)‖ ≤ ε)
    (hζc : ContinuousOn ζ {L : Radius | L₀ ≤ L.1})
    (hπc : Continuous (fun p : Radius × FourierL2 => π p.1 p.2)) :
    HasContinuousTorusCoordinateData (F := F) T A π := by
  obtain ⟨K, hK, hscale⟩ := exists_uniform_frame_scale (E := FourierL2) (F := F) C CA C hC hCA hC
  let ζ' := fun L => stableNormalizedFrame K (ζ L)
  let B := 1 + C + K * Cπ
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨K, hK, B, hB, L₀, ζ', D, R, hinv, hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL v
    exact stableNormalized_rightInverse K hK.ne' (ζ L) (π L) (hframe L hL).1 v
  · intro L hL
    have hLR := hL.trans (torusEndpointRadius_ge T L)
    obtain ⟨_, hζ, hπ, hP⟩ := hframe L hL
    obtain ⟨_, _, _, hPR⟩ := hframe (torusEndpointRadius T L) hLR
    obtain ⟨hζ', hmixed⟩ := hscale (ζ L) (ζ (torusEndpointRadius T L))
      (π (torusEndpointRadius T L)) (A L) hPR (hA L) hζ
    refine ⟨hζ', ?_, ?_, ?_, hmixed⟩
    · exact (stableNormalizedCoordinate_norm_le K Cπ hK.le (π L) hπ).trans (by dsimp [B]; linarith)
    · change ‖stableFrameProjection (stableNormalizedFrame K (ζ L))
        (stableNormalizedCoordinate K (π L))‖ ≤ B
      rw [stableNormalized_projection K hK.ne']
      exact hP.trans (by dsimp [B]; nlinarith [mul_nonneg hK.le hCπ])
    · change ‖stableProjectedBlock (stableNormalizedFrame K (ζ L))
        (stableNormalizedFrame K (ζ (torusEndpointRadius T L)))
        (stableNormalizedCoordinate K (π L))
        (stableNormalizedCoordinate K (π (torusEndpointRadius T L))) (A L)‖ ≤ 1 / 8
      rw [stableNormalized_projectedBlock K hK.ne']
      exact hstable L hL
  · intro ε hε
    obtain ⟨Lε, hεL⟩ := hdefect (ε / K) (div_pos hε hK)
    refine ⟨max L₀ Lε, le_max_left _ _, ?_⟩
    intro L hL
    apply (stableNormalized_defect_norm_le K (ε / K) hK.le (π L)
      (π (torusEndpointRadius T L)) (A L) D
      (hεL L ((le_max_right _ _).trans hL))).trans_eq
    exact mul_div_cancel₀ ε hK.ne'

  · change ContinuousOn (fun L => (K⁻¹ : ℝ) • ζ L) {L : Radius | L₀ ≤ L.1}
    exact (continuousOn_const : ContinuousOn (fun _ : Radius => (K⁻¹ : ℝ))
      {L : Radius | L₀ ≤ L.1}).smul hζc
  · change Continuous (fun p : Radius × FourierL2 => (K : ℝ) • π p.1 p.2)
    exact continuous_const.smul hπc

theorem continuous_torusCoordinateData_discrete {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (κ : Radius → FourierL2 →L[ℝ] F)
    (h : HasContinuousTorusCoordinateData (F := F) T A κ) :
    ∃ K : ℝ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ,
      ∃ ζ : Radius → ℕ → F →L[ℝ] FourierL2,
      ∃ π : Radius → ℕ → FourierL2 →L[ℝ] F,
      (∀ L n, π L n = K • κ (expandingDiscreteRadius L T n)) ∧
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
  obtain ⟨K, hK, C, hC, Lb, ζ, D, R, hinv, hR, hframe, hbound, hdefect, hζc, hπc⟩ := h
  let π := fun L => K • κ L
  refine ⟨K, hK, C, hC, ?_⟩
  intro ε hε
  obtain ⟨L₀, hLb, hεL⟩ := hdefect ε hε
  refine ⟨L₀, (fun L n => ζ (expandingDiscreteRadius L T n)),
    (fun L n => π (expandingDiscreteRadius L T n)), (fun _ _ => rfl), D, R, hinv, hR, ?_, ?_, ?_⟩
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
