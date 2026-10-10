import OAI.Geometry.EinsteinFour.OrientationCoverTangent

namespace OAI

/-! The actual pullback Riemannian metric on the orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local notation "V" => FourSpace
local notation "B" => (V →L[ℝ] V →L[ℝ] ℝ)

private theorem orientationCover_bilinear_coordinates (x y : OrientationCover M)
    (hy : y ∈ (chartAt V x).source) (b : B) :
    (trivializationAt B (fun z : OrientationCover M => TangentSpace I4 z →L[ℝ]
      TangentSpace I4 z →L[ℝ] ℝ) x ⟨y, b⟩).2 =
    (trivializationAt B (fun z : M => TangentSpace I4 z →L[ℝ]
      TangentSpace I4 z →L[ℝ] ℝ) x.proj ⟨y.proj, b⟩).2 := by
  have hb : y.proj ∈ (chartAt V x.proj).source := by
    have h : orientationCoverLocal x y ∈ (chartAt V x.proj).source := hy.2
    simpa only [orientationCoverLocal_apply] using h
  simp only [hom_trivializationAt_apply]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have h₁ := inCoordinates_apply_eq₂ (ϕ :=
    (show TangentSpace I4 y →L[ℝ] TangentSpace I4 y →L[ℝ] ℝ from b))
    (v := v) (w := w)
    (show y ∈ (trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).baseSet from hy)
    (show y ∈ (trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).baseSet from hy)
    (show y ∈ (trivializationAt ℝ (Bundle.Trivial (OrientationCover M) ℝ) x).baseSet from by simp)
  have h₂ := inCoordinates_apply_eq₂ (ϕ :=
    (show TangentSpace I4 y.proj →L[ℝ] TangentSpace I4 y.proj →L[ℝ] ℝ from b))
    (v := v) (w := w)
    (show y.proj ∈ (trivializationAt V (TangentSpace I4 : M → Type _) x.proj).baseSet from hb)
    (show y.proj ∈ (trivializationAt V (TangentSpace I4 : M → Type _) x.proj).baseSet from hb)
    (show y.proj ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) x.proj).baseSet from by simp)
  apply h₁.trans
  apply Eq.trans _ h₂.symm
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_apply]
  change b ((trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).symm y v)
    ((trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x).symm y w) =
    b ((trivializationAt V (TangentSpace I4 : M → Type _) x.proj).symm y.proj v)
    ((trivializationAt V (TangentSpace I4 : M → Type _) x.proj).symm y.proj w)
  simp only [← Trivialization.symmL_apply (R := ℝ)
    (trivializationAt V (TangentSpace I4 : OrientationCover M → Type _) x) hy,
    ← Trivialization.symmL_apply (R := ℝ)
      (trivializationAt V (TangentSpace I4 : M → Type _) x.proj) hb,
    orientationCover_tangent_inverse_trivialization x y hy]
  rfl



/-- In the preferred coordinates the derivative of the covering projection is
identity, so the pullback inner product is the actual base inner product. -/
def orientationCoverMetric (g : SmoothMetric M) : SmoothMetric (OrientationCover M) where
  inner x := g.inner x.proj
  symm x := g.symm x.proj
  pos x := g.pos x.proj
  isVonNBounded x := g.isVonNBounded x.proj
  contMDiff := by
    intro x
    apply (contMDiffAt_section (s := fun y : OrientationCover M =>
      (show TangentSpace I4 y →L[ℝ] TangentSpace I4 y →L[ℝ] ℝ from g.inner y.proj)) x).mpr
    have hg := (contMDiffAt_section (s := g.inner) x.proj).mp (g.contMDiff x.proj)
    have hc := hg.comp x (orientationCover_projection_smooth x)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(chartAt V x).open_source.mem_nhds (mem_chart_source V x)] with y hy
    exact orientationCover_bilinear_coordinates x y hy (g.inner y.proj)

@[simp] theorem orientationCoverMetric_inner (g : SmoothMetric M) (x : OrientationCover M)
    (v w : FourSpace) : (orientationCoverMetric g).inner x v w = g.inner x.proj v w := rfl

theorem orientationCoverMetric_pullback (g : SmoothMetric M) (x : OrientationCover M)
    (v w : TangentSpace I4 x) :
    (orientationCoverMetric g).inner x v w = g.inner x.proj
      (mfderiv I4 I4 orientationCoverProjection x v)
      (mfderiv I4 I4 orientationCoverProjection x w) := by
  rw [orientationCover_projection_mfderiv]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
