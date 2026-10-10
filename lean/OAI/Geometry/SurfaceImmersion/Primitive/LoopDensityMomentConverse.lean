import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityMoments

namespace OAI

/-! Recombine mass and vector mean into the augmented linear moment equation. -/
noncomputable section

namespace ClosedSurfaceR4.LoopDensity

lemma augmented_moments {ρ : ℝ → ℝ} {p : ℝ → Plane} {c : Plane}
    (hρ : Continuous ρ) (hp : Continuous p)
    (hmass : (∫ t in 0..1, ρ t) = 1)
    (hmean : (∫ t in 0..1, ρ t • p t) = c) :
    (∫ t in 0..1, ρ t • augment (p t)) = augment c := by
  have hi : IntervalIntegrable (fun t => ρ t • augment (p t)) MeasureTheory.volume 0 1 :=
    (hρ.smul (augment_continuous.comp hp)).intervalIntegrable 0 1
  have hpi : IntervalIntegrable (fun t => ρ t • p t) MeasureTheory.volume 0 1 :=
    (hρ.smul hp).intervalIntegrable 0 1
  have hc (i : Fin 2) : (∫ t in 0..1, (ρ t • p t) i) = c i := by
    have he := congrArg (fun x : Plane => x i) hmean
    have hev : (∫ t in 0..1, ρ t • p t) i = ∫ t in 0..1, (ρ t • p t) i :=
      ((ContinuousLinearMap.proj i : Plane →L[ℝ] ℝ).intervalIntegral_comp_comm hpi).symm
    rwa [hev] at he
  ext i
  have hev : (∫ t in 0..1, ρ t • augment (p t)) i =
      ∫ t in 0..1, (ρ t • augment (p t)) i :=
    ((ContinuousLinearMap.proj i : Moments →L[ℝ] ℝ).intervalIntegral_comp_comm hi).symm
  rw [hev]
  fin_cases i
  · simpa [augment] using hmass
  · simpa [augment] using hc 0
  · simpa [augment] using hc 1

end ClosedSurfaceR4.LoopDensity

end

end OAI
