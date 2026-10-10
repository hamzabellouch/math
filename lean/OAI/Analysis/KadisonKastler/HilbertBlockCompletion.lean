import OAI.Analysis.KadisonKastler.ComplementaryContractionLift
import OAI.Analysis.KadisonKastler.HilbertDefect

namespace OAI

/-! # Contractive completion of a Hilbert-space operator block

A contractive row and a contractive column with the same corner have a
common contractive completion. The construction uses the defect isometry
and the complementary lift, and is the finite completion step for nests.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def firstCoordinateIsometry : F →ₗᵢ[ℂ] WithLp 2 (F × E) where
  toFun y := WithLp.toLp 2 (y, 0)
  map_add' x y := by simp [← WithLp.toLp_add]
  map_smul' c x := by simp [← WithLp.toLp_smul]
  norm_map' y := WithLp.norm_toLp_fst 2 F E y

theorem firstCoordinateIsometry_adjoint (z : WithLp 2 (F × E)) :
    (firstCoordinateIsometry (E := E) (F := F)).toContinuousLinearMap.adjoint z = z.fst := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [firstCoordinateIsometry, WithLp.prod_inner_apply]

theorem exists_contractive_block_completion
    (A : E →L[ℂ] F) (B : G →L[ℂ] F) (C : E →L[ℂ] H)
    (hrow : ∀ y, ‖A.adjoint y‖ ^ 2 + ‖B.adjoint y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hcol : ∀ x, ‖A x‖ ^ 2 + ‖C x‖ ^ 2 ≤ ‖x‖ ^ 2) :
    ∃ D : G →L[ℂ] H, ∀ x z,
      ‖A x + B z‖ ^ 2 + ‖C x + D z‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖z‖ ^ 2 := by
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [hcol x, sq_nonneg ‖C x‖]
  let V := defectIsometry A hA
  let J : F →ₗᵢ[ℂ] WithLp 2 (F × E) := firstCoordinateIsometry
  have hJV : J.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap = A := by
    ext x
    rw [ContinuousLinearMap.comp_apply, firstCoordinateIsometry_adjoint]
    rfl
  have hVJ (y : F) : V.toContinuousLinearMap.adjoint (J y) = A.adjoint y := by
    have h := congrArg ContinuousLinearMap.adjoint hJV
    have hp := congrArg (fun T : F →L[ℂ] E => T y) h
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap] using hp
  obtain ⟨Y, hY, hJY, hVY⟩ := exists_complementary_contraction_lift V J B (by
    intro y
    rw [hVJ]
    exact hrow y)
  have hCD (x : E) : ‖C x‖ ≤ ‖operatorDefect A x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_operatorDefect_sq A hA]
    linarith [hcol x]
  obtain ⟨R, hR, hRD⟩ := exists_contraction_factor (operatorDefect A) C hCD
  let D := R.comp ((WithLp.sndL 2 ℂ F E).comp Y)
  refine ⟨D, ?_⟩
  intro x z
  let w := V x + Y z
  have hw₁ : w.fst = A x + B z := by
    have h := congrArg (fun T : G →L[ℂ] F => T z) hJY
    rw [ContinuousLinearMap.comp_apply, firstCoordinateIsometry_adjoint] at h
    change A x + (Y z).fst = A x + B z
    rw [h]
  have hw₂ : R w.snd = C x + D z := by
    have h := congrArg (fun T : E →L[ℂ] H => T x) hRD
    change R (operatorDefect A x) = C x at h
    change R (operatorDefect A x + (Y z).snd) = C x + R (Y z).snd
    rw [map_add, h]
  have horth : inner ℂ (V x) (Y z) = 0 := by
    change inner ℂ (V.toContinuousLinearMap x) (Y z) = 0
    rw [← V.toContinuousLinearMap.adjoint_inner_right]
    have h := congrArg (fun T : G →L[ℂ] E => T z) hVY
    change V.toContinuousLinearMap.adjoint (Y z) = 0 at h
    rw [h, inner_zero_right]
  have hnY : ‖Y z‖ ≤ ‖z‖ := by
    simpa only [one_mul] using Y.le_of_opNorm_le hY z
  have hnR : ‖R w.snd‖ ≤ ‖w.snd‖ := by
    simpa only [one_mul] using R.le_of_opNorm_le hR w.snd
  calc
    _ = ‖w.fst‖ ^ 2 + ‖R w.snd‖ ^ 2 := by rw [hw₁, hw₂]
    _ ≤ ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 := by gcongr
    _ = ‖w‖ ^ 2 := (WithLp.prod_norm_sq_eq_of_L2 w).symm
    _ = ‖x‖ ^ 2 + ‖Y z‖ ^ 2 := by
      change ‖V x + Y z‖ ^ 2 = _
      rw [norm_add_sq (𝕜 := ℂ), horth, V.norm_map]
      simp
    _ ≤ ‖x‖ ^ 2 + ‖z‖ ^ 2 := by gcongr

end

end KadisonKastler

end OAI
