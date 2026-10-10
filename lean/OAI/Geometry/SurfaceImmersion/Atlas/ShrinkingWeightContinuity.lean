import OAI.Geometry.SurfaceImmersion.Primitive.ShrinkingCircularWeight

namespace OAI

/-! Uniform convergence of the actual ratio cutoffs from smaller radii.
The upper clamp permits an ordinary product-neighborhood argument at the
original radius, including the boundary where numerator and denominator vanish. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularManifoldBump_joint_continuousAt_of_source (p : M) (r : ℝ) {x : M}
    (hx : x ∈ (coordinateChart p).source) :
    ContinuousAt (fun z : ℝ × M => circularManifoldBump p z.1 z.2) (r,x) := by
  classical
  have hc := ((coordinateChart p).continuousOn.continuousAt
    ((coordinateChart p).open_source.mem_nhds hx)).comp (x := (r,x))
      continuous_snd.continuousAt
  have hg : ContinuousAt (fun z : ℝ × M =>
      ((coordinateChart p p,z.1),coordinateChart p z.2)) (r,x) :=
    (continuousAt_const.prodMk continuous_fst.continuousAt).prodMk hc
  have hf := circularFlatBump_joint_smooth.continuous.continuousAt.comp (x := (r,x)) hg
  apply hf.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually
    ((coordinateChart p).open_source.mem_nhds hx)] with z hz
  exact indicator_of_mem hz _

def shrinkingRadius (r0 r : ℝ) : ℝ := max 0 (min r0 r)

lemma shrinkingRadius_bounds {r0 : ℝ} (hr0 : 0 ≤ r0) (r : ℝ) :
    0 ≤ shrinkingRadius r0 r ∧ shrinkingRadius r0 r ≤ r0 := by
  exact ⟨le_max_left _ _,max_le hr0 (min_le_left _ _)⟩

lemma shrinkingRadius_of_mem {r0 r : ℝ} (hr : 0 ≤ r) (hr0 : r ≤ r0) :
    shrinkingRadius r0 r = r := by
  simp only [shrinkingRadius,min_eq_right hr0,max_eq_right hr]

lemma shrinkingRadius_continuous (r0 : ℝ) : Continuous (shrinkingRadius r0) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Joint continuity remains valid at a vanishing denominator, because the
ratio cutoff lies between zero and the original continuous weight. -/
theorem shrinkingCircularWeight_joint_continuousAt_reference (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) (hnon : ∀ x, 0 ≤ w x) {r0 : ℝ}
    (hr0 : 0 < r0)
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0) (x : M) :
    ContinuousAt (fun z : ℝ × M =>
      shrinkingCircularWeight p w r0 (shrinkingRadius r0 z.1) z.2) (r0,x) := by
  have hclip := shrinkingRadius_of_mem hr0.le (le_refl r0)
  have href := congrFun (shrinkingCircularWeight_reference p w r0 hnon hpos) x
  have hb := (circularManifoldBump_smooth_support p r0 hreg0).1.continuous
  by_cases hp : 0 < circularManifoldBump p r0 x
  · have hx := ((circularManifoldBump_pos_iff p x r0).mp hp).1
    have hc : ContinuousAt (fun z : ℝ × M => (shrinkingRadius r0 z.1,z.2)) (r0,x) :=
      (((shrinkingRadius_continuous r0).comp continuous_fst).prodMk continuous_snd).continuousAt
    have ho : ContinuousAt (fun z : ℝ × M => circularManifoldBump p z.1 z.2)
        (shrinkingRadius r0 r0,x) := by
      rw [hclip]
      exact circularManifoldBump_joint_continuousAt_of_source p r0 hx
    have hn := ho.comp (x := (r0,x)) hc
    exact (hw.continuous.comp continuous_snd).continuousAt.mul
      (hn.div (hb.comp continuous_snd).continuousAt hp.ne')
  · have hz : w x = 0 := le_antisymm (le_of_not_gt (fun hwx => hp
      ((circularManifoldBump_pos_iff p x r0).mpr ((hpos x).mp hwx)))) (hnon x)
    have hu : Tendsto (fun z : ℝ × M => w z.2) (𝓝 (r0,x)) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℝ × M => w z.2) (r0,x) :=
        (hw.continuous.comp continuous_snd).continuousAt
      change Tendsto (fun z : ℝ × M => w z.2) (𝓝 (r0,x)) (𝓝 (w x)) at hc
      rw [hz] at hc
      exact hc
    have hs : Tendsto (fun z : ℝ × M =>
        shrinkingCircularWeight p w r0 (shrinkingRadius r0 z.1) z.2)
        (𝓝 (r0,x)) (𝓝 0) := by
      apply tendsto_const_nhds.squeeze hu
      · intro z
        have hc := shrinkingRadius_bounds hr0.le z.1
        exact (shrinkingCircularWeight_nonneg_le p w hnon
          (show (shrinkingRadius r0 z.1)^2 ≤ r0^2 by nlinarith) z.2).1
      · intro z
        have hc := shrinkingRadius_bounds hr0.le z.1
        exact (shrinkingCircularWeight_nonneg_le p w hnon
          (show (shrinkingRadius r0 z.1)^2 ≤ r0^2 by nlinarith) z.2).2
    simpa only [ContinuousAt,hclip,href,hz] using hs

variable [CompactSpace M]

/-- Independent smaller radii can be chosen in one left neighborhood while
preserving the weight uniformly on the entire compact manifold. -/
theorem shrinkingCircularWeight_uniform_perturbation (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) (hnon : ∀ x, 0 ≤ w x) {r0 : ℝ}
    (hr0 : 0 < r0)
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ r0 / 2 ∧ ∀ r : ℝ,
      r0-delta < r → r < r0 →
      ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight p w r0 r) ∧
      (∀ x, 0 < shrinkingCircularWeight p w r0 r x ↔ x ∈ circularCoordinateDisk p r) ∧
      tsupport (shrinkingCircularWeight p w r0 r) ⊆ circularDiskClosure p r ∧
      ∀ x, |shrinkingCircularWeight p w r0 r x-w x| < eps := by
  have hv : ∀ᶠ r in 𝓝 r0, ∀ x : M,
      |shrinkingCircularWeight p w r0 (shrinkingRadius r0 r) x-w x| < eps := by
    have hv' : ∀ᶠ r in 𝓝 r0, ∀ x ∈ (univ : Set M),
        |shrinkingCircularWeight p w r0 (shrinkingRadius r0 r) x-w x| < eps := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro x _
      have hc := ((shrinkingCircularWeight_joint_continuousAt_reference
        p w hw hnon hr0 hreg0 hpos x).sub
        (hw.continuous.comp continuous_snd).continuousAt).abs
      have hz : |shrinkingCircularWeight p w r0 (shrinkingRadius r0 r0) x-w x| < eps := by
        rw [shrinkingRadius_of_mem hr0.le le_rfl,
          shrinkingCircularWeight_reference p w r0 hnon hpos,sub_self,abs_zero]
        exact heps
      exact hc.eventually (gt_mem_nhds hz)
    exact hv'.mono (fun r hh x => hh x (mem_univ x))
  obtain ⟨d,hd,hnear⟩ := Metric.eventually_nhds_iff.mp hv
  refine ⟨min d (r0/2),lt_min hd (half_pos hr0),min_le_right _ _,?_⟩
  intro r hr hrmax
  have hrpos : 0 < r := by have := min_le_right d (r0/2); linarith
  have hs : r^2 < r0^2 := by nlinarith
  have hsm := shrinkingCircularWeight_smooth p w hw hreg0 hs
  refine ⟨hsm.1,shrinkingCircularWeight_pos_iff p w hnon hs.le hpos,hsm.2,?_⟩
  have habs : |r-r0| < d := by
    rw [abs_of_neg (sub_neg.mpr hrmax)]
    have := min_le_left d (r0/2)
    linarith
  simpa only [shrinkingRadius_of_mem hrpos.le hrmax.le] using
    hnear (y := r) (by simpa only [Real.dist_eq] using habs)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
