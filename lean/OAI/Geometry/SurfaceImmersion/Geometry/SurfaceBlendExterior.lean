import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceBlendGerms

namespace OAI

/-! The scalar cutoff gives exact smooth chart germs outside the transition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

lemma surfaceTimeBlend_left_germ (c d : SurfaceTimeChart F)
    (hF : Continuous F) {l r : ℝ} (hlr : l < r) {x : M} (hx : F x < l) :
    surfaceTimeBlend c d (timeCutoff l r) =ᶠ[𝓝 x] c.coord := by
  filter_upwards [hF.continuousAt.eventually (isOpen_Iio.mem_nhds hx)] with y hy
  exact surfaceTimeBlend_zero c d (timeCutoff_zero hlr hy.le)

lemma surfaceTimeBlend_right_germ (c d : SurfaceTimeChart F)
    (hF : Continuous F) {l r : ℝ} (hlr : l < r) {x : M} (hx : r < F x) :
    surfaceTimeBlend c d (timeCutoff l r) =ᶠ[𝓝 x] d.coord := by
  filter_upwards [hF.continuousAt.eventually (isOpen_Ioi.mem_nhds hx)] with y hy
  exact surfaceTimeBlend_one c d (timeCutoff_one hlr hy.le)

lemma SurfaceTimeChart.regular (c : SurfaceTimeChart F) {x : M}
    (hx : x ∈ c.coord.source) :
    Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) c.coord x) := by
  have hD : c.coord.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  exact hD.mfderiv_bijective hx

lemma straddling_compact_interval {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {V : Set ℝ} (hV : V ∈ 𝓝 b) :
    ∃ l r, a < l ∧ l < b ∧ b < r ∧ r < c ∧ Icc l r ⊆ V := by
  obtain ⟨s,t,hbst,hst⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem hV (Ioo_mem_nhds hab hbc))
  have hs : a < b := hab
  have hsa : a < t := (hst ⟨hbst.1,hbst.2⟩).2.1.trans hbst.2
  let l := (max a s + b)/2
  let r := (b + min c t)/2
  have hmax : max a s < b := max_lt hab hbst.1
  have hmin : b < min c t := lt_min hbc hbst.2
  refine ⟨l,r,?_,?_,?_,?_,?_⟩
  · dsimp [l]; have := le_max_left a s; linarith
  · dsimp [l]; linarith
  · dsimp [r]; linarith
  · dsimp [r]; have := min_le_left c t; linarith
  · intro x hx
    apply (hst ?_).1
    constructor
    · have := le_max_right a s; dsimp [l] at hx; linarith [hx.1]
    · have := min_le_right c t; dsimp [r] at hx; linarith [hx.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
