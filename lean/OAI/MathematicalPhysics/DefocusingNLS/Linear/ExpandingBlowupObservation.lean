import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalTrajectory
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffApproximateMode
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SimilarityLimit

namespace OAI

/-! # Point observations of the actual similarity perturbation

The center of the sampled cutoff profile equals `Q 0` exactly.  The uniform
expanding-space evaluation bound therefore transfers norm decay to the
pointwise convergence required by the manuscript's final blowup statement.
-/

open Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingInverseTransfer_function (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R) (f : FourierL2) :
    expandingTorusFunction a k 1 (expandingInverseTransfer a k R ha hk hR f) =
      expandingTorusFunction a k R f := by
  have he : expandingScaleTransfer a k 1 R ha hk le_rfl hR
      (expandingInverseTransfer a k R ha hk hR f) = f :=
    congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A f)
      (expandingWeightUnit a k R ha hk hR).val_inv
  have h := expandingScaleTransfer_function a k 1 R ha ha1 hk le_rfl hR
    (expandingInverseTransfer a k R ha hk hR f)
  rw [he] at h
  exact h.symm

theorem expandingSobolev_observation (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R)
    (f : FourierL2) (x : SchrodingerTorus) :
    sobolevTorusFunction k
        (expandingToSobolev a k ha1 hk (expandingInverseTransfer a k R ha hk hR f)) x =
      expandingTorusFunction a k R f x := by
  rw [sobolevTorusFunction_expandingToSobolev a k ha ha1 hk,
    expandingInverseTransfer_function a k R ha ha1 hk hR]

theorem sampledCutoffProfile_center (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    expandingTorusFunction a k R (schwartzTorusSample a k R ha1 hk hR
      (radianFourierKernel (cutoffProfileSchwartz R (by linarith)
        (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ))) 0 = Q 0 := by
  have h := schwartzTorusSample_eq_on_ball a k R ha ha1 hk hR
    (cutoffProfileSchwartz R (by linarith) (χ.postcompCLM Complex.ofRealCLM)
      (hasCompactSupport_complexCutoff χ hχ) Q hQ)
    (cutoffProfileSchwartz_zero_outside R (by linarith) χ hχ hχzero Q hQ)
    (0 : E) (by simpa using (zero_le_one.trans hR))
  have hχ0 : χ 0 = 1 := hχone 0 (by norm_num)
  have hz : euclideanToTorus (0 : E) = 0 := by
    ext j
    simp [euclideanToTorus]
  simpa [hz, cutoffProfileSchwartz_apply, hχ0] using h

theorem expanding_observation_difference_le (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R)
    (f g : FourierL2) (x : SchrodingerTorus) :
    ‖expandingTorusFunction a k R f x - expandingTorusFunction a k R g x‖ ≤
      expandingEmbeddingBound a k * ‖f - g‖ := by
  rw [expandingTorusFunction_eq_evaluation a k R ha ha1 hk hR,
    expandingTorusFunction_eq_evaluation a k R ha ha1 hk hR, ← map_sub]
  exact (expandingPointEvaluation a k R ha ha1 hk hR x).le_opNorm (f - g) |>.trans
    (mul_le_mul_of_nonneg_right (expandingPointEvaluation_norm_le a k R ha ha1 hk hR x)
      (norm_nonneg _))

/-- Decay of the similarity perturbation determines the limiting point observation. -/
theorem expanding_observation_tendsto_of_norm_decay (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u q : ℝ → FourierL2) (x : SchrodingerTorus) (c : ℂ)
    (hq : ∀ s, 0 ≤ s → expandingTorusFunction a k (expandingRadius L s) (q s) x = c)
    (hdecay : Tendsto (fun s => ‖u s - q s‖) atTop (𝓝 0)) :
    Tendsto (fun s => expandingTorusFunction a k (expandingRadius L s) (u s) x)
      atTop (𝓝 c) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun s => expandingEmbeddingBound a k * ‖u s - q s‖) atTop (𝓝 0) := by
    simpa using hdecay.const_mul (expandingEmbeddingBound a k)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  rw [← hq s hs]
  exact expanding_observation_difference_le a k (expandingRadius L s) ha ha1 hk
    (hL.trans (expandingRadius_ge L s hL hs)) (u s) (q s) x

end DefocusingNLS

end OAI
