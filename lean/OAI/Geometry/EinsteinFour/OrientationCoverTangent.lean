import OAI.Geometry.EinsteinFour.OrientationCoverProjection

namespace OAI

/-! Tangent trivializations on each sheet agree with the base trivializations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_tangent_trivialization (x y : OrientationCover M)
    (hy : y ∈ (chartAt FourSpace x).source) :
    (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x).continuousLinearMapAt ℝ y =
      (trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj).continuousLinearMapAt ℝ y.proj := by
  have hb : y.proj ∈ (chartAt FourSpace x.proj).source := by
    have h : orientationCoverLocal x y ∈ (chartAt FourSpace x.proj).source := hy.2
    simpa only [orientationCoverLocal_apply] using h
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.continuousLinearMapAt_trivializationAt hb]
  have he : (extChartAt I4 x : OrientationCover M → FourSpace) =
      extChartAt I4 x.proj ∘ orientationCoverProjection := by
    funext z
    simp only [extChartAt_coe, Function.comp_apply]
    rw [show chartAt FourSpace x z = chartAt FourSpace x.proj z.proj from
      orientationCoverChart_apply x z]
  rw [he, mfderiv_comp y (mdifferentiableAt_extChartAt hb)
    (orientationCover_projection_hasMFDerivAt y).mdifferentiableAt,
    orientationCover_projection_mfderiv]
  rfl

theorem orientationCover_tangent_inverse_trivialization (x y : OrientationCover M)
    (hy : y ∈ (chartAt FourSpace x).source) :
    (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x).symmL ℝ y =
      (trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj).symmL ℝ y.proj := by
  let a := trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x
  let b := trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj
  have ha : y ∈ a.baseSet := hy
  have hb : y.proj ∈ b.baseSet := by
    change y.proj ∈ (chartAt FourSpace x.proj).source
    have h : orientationCoverLocal x y ∈ (chartAt FourSpace x.proj).source := hy.2
    simpa only [orientationCoverLocal_apply] using h
  have hf := orientationCover_tangent_trivialization x y hy
  apply ContinuousLinearMap.ext
  intro v
  have h₁ : b.symmL ℝ y.proj (b.continuousLinearMapAt ℝ y.proj (a.symmL ℝ y v)) =
      a.symmL ℝ y v := b.symmL_continuousLinearMapAt hb _
  have h₂ : b.continuousLinearMapAt ℝ y.proj (a.symmL ℝ y v) = v := by
    rw [← hf]
    exact a.continuousLinearMapAt_symmL ha v
  exact h₁.symm.trans (congrArg (fun z : FourSpace => b.symmL ℝ y.proj z) h₂)

end
end PositiveEinsteinFour.Geometry

end OAI
