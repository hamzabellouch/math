import OAI.Geometry.SurfaceImmersion.Correction.CircularSmoothingAtlas

namespace OAI

/-! Actual independent radius perturbations of circular manifold cutoffs.
A fixed larger disk supplies common support and uniform continuity. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularCoordinateRegion_mono (p : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularCoordinateRegion p r ⊆ circularCoordinateRegion p R := by
  intro x hx
  exact hx.trans h

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_mono (p : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularDiskClosure p r ⊆ circularDiskClosure p R :=
  image_mono (circularCoordinateRegion_mono p h)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularManifoldBump_zero_off_larger_disk (p : M) {r R : ℝ} (hr : r^2 ≤ R^2)
    {x : M} (hx : x ∉ circularDiskClosure p R) : circularManifoldBump p r x = 0 := by
  classical
  by_cases hs : x ∈ (coordinateChart p).source
  · rw [circularManifoldBump,indicator_of_mem hs]
    apply (circularFlatBump_zero_iff _ _ _).mpr
    by_contra hn
    apply hx
    exact ⟨coordinateChart p x, (not_le.mp hn).le.trans hr,
      (coordinateChart p).left_inv hs⟩
  · simp only [circularManifoldBump,indicator_of_notMem hs]

omit [IsManifold planeModel ∞ M] in
/-- The radius and base point vary continuously together, including at the
chart boundary where the common compact support forces the cutoff to vanish. -/
lemma circularManifoldBump_joint_continuousAt (p : M) {R r : ℝ}
    (hregion : circularCoordinateRegion p R ⊆ (coordinateChart p).target)
    (hr : |r| < R) (x : M) :
    ContinuousAt (fun z : ℝ × M => circularManifoldBump p z.1 z.2) (r,x) := by
  classical
  by_cases hs : x ∈ (coordinateChart p).source
  · have hc := ((coordinateChart p).continuousOn.continuousAt
      ((coordinateChart p).open_source.mem_nhds hs)).comp (x := (r,x))
        continuous_snd.continuousAt
    have hg : ContinuousAt (fun z : ℝ × M =>
        ((coordinateChart p p,z.1),coordinateChart p z.2)) (r,x) :=
      (continuousAt_const.prodMk continuous_fst.continuousAt).prodMk hc
    have hf := circularFlatBump_joint_smooth.continuous.continuousAt.comp (x := (r,x)) hg
    apply hf.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually
      ((coordinateChart p).open_source.mem_nhds hs)] with z hz
    exact indicator_of_mem hz _
  · have hK := circularDiskClosure_compact p R hregion
    have hx : x ∉ circularDiskClosure p R := fun hx =>
      hs (circularDiskClosure_source p R hregion hx)
    have hrad : r^2 < R^2 := by
      have hR : 0 < R := (abs_nonneg r).trans_lt hr
      nlinarith [sq_abs r, abs_nonneg r]
    have hn : ∀ᶠ z : ℝ × M in 𝓝 (r,x), z.1^2 < R^2 :=
      ((continuous_fst.pow 2).continuousAt).eventually (gt_mem_nhds hrad)
    have hk : ∀ᶠ z : ℝ × M in 𝓝 (r,x), z.2 ∉ circularDiskClosure p R :=
      (show ContinuousAt (Prod.snd : ℝ × M → M) (r,x) from continuous_snd.continuousAt).eventually
        (hK.isClosed.isOpen_compl.mem_nhds hx)
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ × M => (0 : ℝ)) (r,x)).congr_of_eventuallyEq
    filter_upwards [hn,hk] with z hz hzK
    exact circularManifoldBump_zero_off_larger_disk p hz.le hzK

variable [CompactSpace M]

/-- Moving one radius slightly gives an actual smooth cutoff with one fixed
compact support and arbitrarily small global C0 error. The radius may be chosen
independently for each member of a later finite family. -/
theorem circularManifoldBump_uniform_perturbation (p : M) {R r : ℝ}
    (hregion : circularCoordinateRegion p R ⊆ (coordinateChart p).target)
    (hr : |r| < R) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r' : ℝ, |r'-r| < delta →
      |r'| < R ∧ ContMDiff planeModel 𝓘(ℝ) ∞ (circularManifoldBump p r') ∧
      tsupport (circularManifoldBump p r') ⊆ circularDiskClosure p R ∧
      ∀ x : M, |circularManifoldBump p r' x-circularManifoldBump p r x| < eps := by
  have hR : 0 < R := (abs_nonneg r).trans_lt hr
  have hsq : r^2 ≤ R^2 := by nlinarith [sq_abs r, abs_nonneg r]
  have hreg := (circularCoordinateRegion_mono p hsq).trans hregion
  have hb := (circularManifoldBump_smooth_support p r hreg).1.continuous
  have hv : ∀ᶠ r' in 𝓝 r, ∀ x : M,
      |circularManifoldBump p r' x-circularManifoldBump p r x| < eps := by
    have hv' : ∀ᶠ r' in 𝓝 r, ∀ x ∈ (univ : Set M),
        |circularManifoldBump p r' x-circularManifoldBump p r x| < eps := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro x _
      have hc := ((circularManifoldBump_joint_continuousAt p hregion hr x).sub
        (hb.comp continuous_snd).continuousAt).abs
      have hzero : |circularManifoldBump p r x-circularManifoldBump p r x| < eps := by
        simpa only [sub_self,abs_zero] using heps
      exact hc.eventually (gt_mem_nhds hzero)
    exact hv'.mono (fun r' hh x => hh x (mem_univ x))
  have hrad : ∀ᶠ r' in 𝓝 r, |r'| < R :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds hr)
  obtain ⟨delta,hdelta,hnear⟩ := Metric.eventually_nhds_iff.mp (hrad.and hv)
  refine ⟨delta,hdelta,fun r' hr' => ?_⟩
  have hh := hnear (y := r') (by simpa only [Real.dist_eq] using hr')
  have hsq' : r'^2 ≤ R^2 := by nlinarith [sq_abs r',abs_nonneg r',hh.1]
  have hreg' := (circularCoordinateRegion_mono p hsq').trans hregion
  have hs := circularManifoldBump_smooth_support p r' hreg'
  exact ⟨hh.1,hs.1,hs.2.trans (circularDiskClosure_mono p hsq'),hh.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
