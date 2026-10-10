import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankAnalytic

namespace OAI

/-! # The finite-dimensional obstruction tends to one at infinity

The same exact determinant that detects the exceptional spectrum is not
identically zero: the ambient resolvent tends to zero in operator norm.
-/

open Filter Topology Bornology

namespace DefocusingNLS

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem finiteRank_determinant_tendsto_one (B : E →L[ℂ] E) (U : F →L[ℂ] E)
    (V : E →L[ℂ] F) :
    Tendsto (fun w : ℂ =>
      (ContinuousLinearMap.id ℂ F - V.comp ((resolvent B w).comp U)).det)
      (cobounded ℂ) (𝓝 1) := by
  let K : (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] F) :=
    (ContinuousLinearMap.compL ℂ F E F V).comp
      ((ContinuousLinearMap.compL ℂ F E E).flip U)
  have hR := spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) B
  have hK := (K.continuous.tendsto 0).comp hR
  have hD : Tendsto (fun w : ℂ => ContinuousLinearMap.id ℂ F - K (resolvent B w))
      (cobounded ℂ) (𝓝 (ContinuousLinearMap.id ℂ F)) := by
    simpa only [Function.comp_def, map_zero, sub_zero] using
      (tendsto_const_nhds (x := ContinuousLinearMap.id ℂ F)).sub hK
  have hd := ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp hD
  have hid : (ContinuousLinearMap.id ℂ F).det = 1 := LinearMap.det_id
  rw [hid] at hd
  simpa only [Function.comp_def, K, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] using hd

theorem finiteRank_determinant_eventually_ne_zero (B : E →L[ℂ] E) (U : F →L[ℂ] E)
    (V : E →L[ℂ] F) :
    ∀ᶠ w : ℂ in cobounded ℂ,
      (ContinuousLinearMap.id ℂ F - V.comp ((resolvent B w).comp U)).det ≠ 0 := by
  exact (finiteRank_determinant_tendsto_one B U V).eventually
    (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))

end

end DefocusingNLS

end OAI
