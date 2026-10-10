import OAI.Analysis.CircleDomains.Probability.GeometricIndexMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Averaging the actual geometric index of a compact arc law. Uniform
bounds come from the ray geometry, rather than a domination hypothesis. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

abbrev ClosedUpperHalfPlane := {z : ℂ // 0 ≤ z.im}

def meanGeometricIndex (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) : ℝ :=
  ∫ γ : K, (geometricRayIndex hsch γ.val (hKS γ.property) z.val : ℝ) ∂(η : Measure K)

 theorem integrable_geometricRayIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) :
    Integrable (fun γ : K => (geometricRayIndex hsch γ.val (hKS γ.property) z.val : ℝ))
      (η : Measure K) := by
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS |z.val.re| z.val.im
    (abs_nonneg _) z.property
  apply Integrable.of_bound
    ((show Continuous (fun n : ℤ => (n : ℝ)) from continuous_of_discreteTopology).measurable.comp
      (measurable_geometricRayIndex hsch hsep K hK hKS z.val z.property)).aestronglyMeasurable M
  apply Eventually.of_forall
  intro γ
  have he := Complex.re_add_im z.val
  simpa only [Function.comp_apply, he, Real.norm_eq_abs] using hM γ z.val.re z.val.im le_rfl z.property le_rfl

 theorem rayIndexDomain_of_projection_avoids (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ClosedUpperHalfPlane)
    (hz : diskRayProjection z.val ∉ range γ) :
    ∀ k : ℤ, halfPlaneDisk z.val ∉ range (translatedHalfPlaneRay γ hγ k).crosscut := by
  intro k hk
  obtain ⟨t, ht⟩ := ((translatedHalfPlaneRay γ hγ k).cayley_mem_crosscut_iff z.property).mp hk
  apply hz
  refine ⟨t.val, ?_⟩
  rw [← diskRayProjection_translated γ hγ k t, ht]

 theorem continuousAt_geometricRayIndex_of_avoids (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ClosedUpperHalfPlane)
    (hz : diskRayProjection z.val ∉ range γ) :
    ContinuousAt (fun w : ClosedUpperHalfPlane =>
      (geometricRayIndex hsch γ hγ w.val : ℝ)) z := by
  let U := {w : ClosedUpperHalfPlane | diskRayProjection w.val ∉ range γ}
  have ho : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl.preimage
    (continuous_diskRayProjection.comp continuous_subtype_val)
  have hc : ContinuousOn (fun w : ClosedUpperHalfPlane =>
      (geometricRayIndex hsch γ hγ w.val : ℝ)) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let f : U → RayIndexDomain γ hγ := fun w => ⟨w.val.val, w.val.property,
      rayIndexDomain_of_projection_avoids γ hγ w.val w.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (show Continuous (fun n : ℤ => (n : ℝ)) from continuous_of_discreteTopology).comp
      ((isLocallyConstant_geometricRayIndex hsch γ hγ).continuous.comp hf)
  exact hc.continuousAt (ho.mem_nhds hz)

 theorem continuousAt_meanGeometricIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane)
    (hz : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection z.val ∉ range γ.val) :
    ContinuousAt (meanGeometricIndex hsch K hKS η) z := by
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; linarith [z.property]
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS X Y hX hY
  have hx : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z, |w.val.re| ≤ X := by
    have hc := (Complex.continuous_re.comp (continuous_subtype_val (p := fun z : ℂ => 0 ≤ z.im))).abs
    have hl : |z.val.re| < X := by dsimp [X]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hl)).mono (fun _ h => h.le)
  have hy : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z, w.val.im ≤ Y := by
    have hc := Complex.continuous_im.comp (continuous_subtype_val (p := fun z : ℂ => 0 ≤ z.im))
    have hl : z.val.im < Y := by dsimp [Y]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hl)).mono (fun _ h => h.le)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ : K => M)
    (Eventually.of_forall fun w =>
      (integrable_geometricRayIndex hsch hsep K hK hKS η w).aestronglyMeasurable)
    ?_ (integrable_const M) ?_
  · filter_upwards [hx, hy] with w hwX hwY
    apply Eventually.of_forall
    intro γ
    have he := Complex.re_add_im w.val
    simpa only [he, Real.norm_eq_abs] using hM γ w.val.re w.val.im hwX w.property hwY
  · filter_upwards [hz] with γ hγ
    exact continuousAt_geometricRayIndex_of_avoids hsch γ.val (hKS γ.property) z hγ

end CircleDomainRigidity

end

end OAI
