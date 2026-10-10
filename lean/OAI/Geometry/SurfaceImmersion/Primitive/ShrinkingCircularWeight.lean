import OAI.Geometry.SurfaceImmersion.Primitive.PerturbedCircularCutoffs

namespace OAI

/-! Weight-preserving independent disk shrinkage. The quotient is only
used where the original bump is positive; the smaller compact support
makes the resulting weight globally smooth. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularManifoldBump_mono_sq (p x : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularManifoldBump p r x ≤ circularManifoldBump p R x := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · simp only [circularManifoldBump,indicator_of_mem hx,circularFlatBump]
    exact expNegInvGlue.monotone (sub_le_sub_right h _)
  · simp only [circularManifoldBump,indicator_of_notMem hx,le_refl]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_subset_disk (p : M) {r R : ℝ} (h : r^2 < R^2)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularDiskClosure p r ⊆ circularCoordinateDisk p R := by
  rintro x ⟨y,hy,rfl⟩
  refine ⟨(coordinateChart p).map_target (hreg hy),?_⟩
  change circularRadiusSquared (coordinateChart p p)
    (coordinateChart p ((coordinateChart p).symm y)) < R^2
  rw [(coordinateChart p).right_inv (hreg hy)]
  exact hy.trans_lt h

/-- The original weight is recovered at the original radius, even though
both circular bumps vanish on and outside its boundary. -/
def shrinkingCircularWeight (p : M) (w : M → ℝ) (r0 r : ℝ) (x : M) : ℝ :=
  w x * (circularManifoldBump p r x / circularManifoldBump p r0 x)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_nonneg_le (p : M) (w : M → ℝ)
    (hw : ∀ x, 0 ≤ w x) {r0 r : ℝ} (hr : r^2 ≤ r0^2) (x : M) :
    0 ≤ shrinkingCircularWeight p w r0 r x ∧ shrinkingCircularWeight p w r0 r x ≤ w x := by
  have hb := circularManifoldBump_mono_sq p x hr
  have hn := circularManifoldBump_nonneg p x r
  have hd := circularManifoldBump_nonneg p x r0
  refine ⟨mul_nonneg (hw x) (div_nonneg hn hd),?_⟩
  by_cases hp : 0 < circularManifoldBump p r0 x
  · exact mul_le_of_le_one_right (hw x) ((div_le_one hp).mpr hb)
  · have hz : circularManifoldBump p r0 x = 0 := le_antisymm (not_lt.mp hp) hd
    simpa only [shrinkingCircularWeight,hz,div_zero,mul_zero] using hw x

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_reference (p : M) (w : M → ℝ) (r0 : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0) :
    shrinkingCircularWeight p w r0 r0 = w := by
  funext x
  by_cases hb : circularManifoldBump p r0 x = 0
  · have hz : w x = 0 := le_antisymm (le_of_not_gt (fun hp =>
      ((circularManifoldBump_pos_iff p x r0).mpr ((hpos x).mp hp)).ne' hb)) (hw x)
    simp only [shrinkingCircularWeight,hz,zero_mul]
  · simp only [shrinkingCircularWeight,div_self hb,mul_one]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_pos_iff (p : M) (w : M → ℝ)
    (_hw : ∀ x, 0 ≤ w x) {r0 r : ℝ} (hr : r^2 ≤ r0^2)
    (hpos : ∀ x, 0 < w x ↔ x ∈ circularCoordinateDisk p r0) (x : M) :
    0 < shrinkingCircularWeight p w r0 r x ↔ x ∈ circularCoordinateDisk p r := by
  constructor
  · intro h
    apply (circularManifoldBump_pos_iff p x r).mp
    apply lt_of_le_of_ne (circularManifoldBump_nonneg p x r)
    intro hb
    have hz : shrinkingCircularWeight p w r0 r x = 0 := by
      simp only [shrinkingCircularWeight,← hb,zero_div,mul_zero]
    exact h.ne' hz
  · intro hx
    have hb := (circularManifoldBump_pos_iff p x r).mpr hx
    have hb0 := hb.trans_le (circularManifoldBump_mono_sq p x hr)
    have hw0 := (hpos x).mpr ((circularManifoldBump_pos_iff p x r0).mp hb0)
    exact mul_pos hw0 (div_pos hb hb0)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_support (p : M) (w : M → ℝ) (r0 r : ℝ) :
    tsupport (shrinkingCircularWeight p w r0 r) ⊆ tsupport (circularManifoldBump p r) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp only [shrinkingCircularWeight,hx,zero_div,mul_zero]

/-- Every strictly smaller radius gives a globally smooth actual weight,
with support in the smaller closed disk. -/
theorem shrinkingCircularWeight_smooth (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 r : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hr : r^2 < r0^2) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight p w r0 r) ∧
      tsupport (shrinkingCircularWeight p w r0 r) ⊆ circularDiskClosure p r := by
  have hreg := (circularCoordinateRegion_mono p hr.le).trans hreg0
  have hb := circularManifoldBump_smooth_support p r hreg
  have hb0 := circularManifoldBump_smooth_support p r0 hreg0
  have hs := (shrinkingCircularWeight_support p w r0 r).trans hb.2
  refine ⟨?_,hs⟩
  apply contMDiff_of_tsupport
  intro x hx
  have hd := (circularDiskClosure_subset_disk p hr hreg) (hs hx)
  have hp := (circularManifoldBump_pos_iff p x r0).mpr hd
  exact (hw x).mul ((hb.1 x).div₀ (hb0.1 x) hp.ne')

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
