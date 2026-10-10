import OAI.Analysis.CircleDomains.Selection.MappedMeanBands
import OAI.Analysis.CircleDomains.Sobolev.CircleSmoothingBands

namespace OAI

/-! The smoothed stream has the same dust bands as the actual mean when
its real correction vanishes there. The width remains the original
point-hit probability. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem perturbed_mapped_mean_bands
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {Y : Type*} [TopologicalSpace Y] (S : Set Y) (s : Y) (hs : s ∈ closure S)
    (L : Y → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) (hproj : diskRayProjection (L s).val = F x)
    (v : Y → ℝ)
    (herr : Tendsto (fun y => v y - meanGeometricIndex hsch K hKS (η.map f) (L y))
      (𝓝[S] s) (𝓝 0)) :
    (liminf v (𝓝[S] s) =
      liminf (fun y => meanGeometricIndex hsch K hKS (η.map f) (L y)) (𝓝[S] s)) ∧
    (limsup v (𝓝[S] s) =
      limsup (fun y => meanGeometricIndex hsch K hKS (η.map f) (L y)) (𝓝[S] s)) ∧
    limsup v (𝓝[S] s) - liminf v (𝓝[S] s) ≤
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  let : NeBot (𝓝[S] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  let u : Y → ℝ := fun y => meanGeometricIndex hsch K hKS (η.map f) (L y)
  let C := ((η.map f : ProbabilityMeasure K) : Measure K).real
    {γ | diskRayProjection (L s).val ∈ range γ.val}
  have hbase := meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS (η.map f)
    (L s) hz zero_lt_one
  have hnear : ∀ᶠ y in 𝓝[S] s, |u y - u s| < C + 1 :=
    (hL.prodMk_nhds tendsto_const_nhds).eventually hbase
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_ge (hnear.mono fun y hy => by
      have hh := (abs_lt.mp hy).1
      exact (show u s - C - 1 ≤ u y by linarith))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_le (hnear.mono fun y hy => by
      have hh := (abs_lt.mp hy).2
      exact (show u y ≤ u s + C + 1 by linarith))
  have heq := bounded_bands_eq_of_sub_tendsto_zero hlo hhi herr
  refine ⟨heq.1, heq.2, ?_⟩
  rw [heq.1, heq.2]
  exact mapped_meanGeometricIndex_band_width hsch hsep A K hK hKS η F f hf hmap
    x hF S s hs L hL hz hproj

end CircleDomainRigidity

end

end OAI
