import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusStableBlocks
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusFrameNormalization

namespace OAI

/-! # Normalized linear data for the discrete stable graph -/

open scoped NNReal

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def HasTorusLinearStep (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∃ ζ : Radius → F →L[ℝ] FourierL2, ∃ π : Radius → FourierL2 →L[ℝ] F,
    ∃ D R : F →L[ℝ] F, (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
      (∀ L : Radius, L₀ ≤ L.1 → ∀ v, π L (ζ L v) = v) ∧
      (∀ L : Radius, L₀ ≤ L.1 →
        ‖ζ L‖ ≤ 1 ∧ ‖π L‖ ≤ C ∧ ‖stableFrameProjection (ζ L) (π L)‖ ≤ C ∧
        ‖stableProjectedBlock (ζ L) (ζ (torusEndpointRadius T L))
          (π L) (π (torusEndpointRadius T L)) (A L)‖ ≤ 1 / 8 ∧
        ‖stableMixedBlock (ζ L) (ζ (torusEndpointRadius T L))
          (π (torusEndpointRadius T L)) (A L)‖ ≤ 1 / 16) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Lε : ℝ, L₀ ≤ Lε ∧ ∀ L : Radius, Lε ≤ L.1 →
        ‖(π (torusEndpointRadius T L)).comp (A L) - D.comp (π L)‖ ≤ ε)

theorem torusLinearStep_of_frames (T : ℝ≥0) (A : Radius → FourierL2 →L[ℝ] FourierL2)
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
      ‖(π (torusEndpointRadius T L)).comp (A L) - D.comp (π L)‖ ≤ ε) :
    HasTorusLinearStep (F := F) T A := by
  obtain ⟨K, hK, hscale⟩ := exists_uniform_frame_scale (E := FourierL2) (F := F) C CA C hC hCA hC
  let ζ' := fun L => stableNormalizedFrame K (ζ L)
  let π' := fun L => stableNormalizedCoordinate K (π L)
  let B := 1 + C + K * Cπ
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, L₀, ζ', π', D, R, hinv, hR, ?_, ?_, ?_⟩
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
    · rw [stableNormalized_projection K hK.ne']
      exact hP.trans (by dsimp [B]; nlinarith [mul_nonneg hK.le hCπ])
    · rw [stableNormalized_projectedBlock K hK.ne']
      exact hstable L hL
  · intro ε hε
    obtain ⟨Lε, hεL⟩ := hdefect (ε / K) (div_pos hε hK)
    refine ⟨max L₀ Lε, le_max_left _ _, ?_⟩
    intro L hL
    apply (stableNormalized_defect_norm_le K (ε / K) hK.le (π L)
      (π (torusEndpointRadius T L)) (A L) D
      (hεL L ((le_max_right _ _).trans hL))).trans_eq
    exact mul_div_cancel₀ ε hK.ne'

end DefocusingNLS

end OAI
