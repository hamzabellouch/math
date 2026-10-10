import OAI.Geometry.Immersion.ClosedSurface.ChartTransition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateInverse_mfderiv_injective (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    Function.Injective (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) := by
  have hxt : x ∈ (coordinateChart p).target := by rwa [coordinateChart_target]
  have hs : coordinateInverse p x ∈ (coordinateChart p).source := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).map_target hxt
  have hi := ((coordinateInverse_smoothOn p) x hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) (coordinateInverse p x) hs).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hs)
  have he : coordinateChart p ∘ coordinateInverse p =ᶠ[𝓝 x] id := by
    filter_upwards [(coordinateDomain_open p).mem_nhds hx] with y hy
    change coordinateChart p (coordinateInverse p y) = y
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).right_inv (by rwa [coordinateChart_target])
  have hd : (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) (coordinateInverse p x)).comp
      (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) =
      ContinuousLinearMap.id ℝ SmallModes.Base := by
    rw [← mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp)),
      he.mfderiv_eq,mfderiv_id]
    rfl
  intro v w hv
  have hvw := congrArg (mfderiv planeModel 𝓘(ℝ,SmallModes.Base)
    (coordinateChart p) (coordinateInverse p x)) hv
  have hdv := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L v) hd
  have hdw := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L w) hd
  exact hdv.symm.trans (hvw.trans hdw)

lemma coordinateMetric_continuousOn (g : SmoothMetric M) (p : M) :
    ContinuousOn (coordinateMetric g p) (coordinateDomain p) := by
  apply continuousOn_pi.mpr
  intro i
  exact metricPullback_continuousOn g (coordinateDomain_open p) (coordinateInverse_smoothOn p) _ _

lemma coordinateMetric_positive (g : SmoothMetric M) (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    0 < coordinateMetric g p x 0 ∧
      0 < coordinateMetric g p x 0 * coordinateMetric g p x 2 - (coordinateMetric g p x 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [coordinateMetric_evaluate]
  exact metricPullback_pos g (coordinateInverse_mfderiv_injective p hx) hv



theorem coordinateMetric_compact_positive (g : SmoothMetric M) (p : M) {K : Set SmallModes.Base}
    (hK : IsCompact K) (hKs : K ⊆ coordinateDomain p) :
    IsCompact (coordinateMetric g p '' K) ∧
      (∀ H ∈ coordinateMetric g p '' K, 0 < H 0) ∧
      (∀ H ∈ coordinateMetric g p '' K, 0 < H 0*H 2-(H 1)^2) := by
  refine ⟨hK.image_of_continuousOn ((coordinateMetric_continuousOn g p).mono hKs),?_,?_⟩
  · rintro H ⟨x,hx,rfl⟩
    exact (coordinateMetric_positive g p (hKs hx)).1
  · rintro H ⟨x,hx,rfl⟩
    exact (coordinateMetric_positive g p (hKs hx)).2

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma metricPullback_smoothOn (g : SmoothMetric M) {φ : Base → M} {O : Set Base}
    (hO : IsOpen O) (hφ : ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ φ O) (v w : Base) :
    ContDiffOn ℝ ∞ (fun x => metricPullback g φ x v w) O := by
  let : RiemannianBundle (fun p : M => TangentSpace planeModel p) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle planeModel ∞ Plane (fun p : M => TangentSpace planeModel p) :=
    ⟨g.inner,g.contMDiff,fun _ _ _ => rfl⟩
  have htm := hφ.contMDiffOn_tangentMapWithin (m := (∞ : ℕ∞ω)) (by simp) hO.uniqueMDiffOn
  have hs (v : Base) : ContMDiff 𝓘(ℝ,Base) (𝓘(ℝ,Base)).tangent ∞ (fun x : Base =>
      (⟨x,v⟩ : TangentBundle 𝓘(ℝ, Base) Base)) := by
    exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hv (v : Base) : ContMDiffOn 𝓘(ℝ,Base) planeModel.tangent ∞ (fun x : Base =>
      (⟨φ x,mfderiv 𝓘(ℝ, Base) planeModel φ x v⟩ : TangentBundle planeModel M)) O := by
    have hh := htm.comp (hs v).contMDiffOn (fun x hx => hx)
    apply hh.congr
    intro x hx
    simp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hO.mem_nhds hx)]
  exact ((hv v).inner_bundle (hv w)).contDiffOn

lemma coordinateMetric_smoothOn (g : SmoothMetric M) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMetric g p) (coordinateDomain p) := by
  apply contDiffOn_pi.mpr
  intro i
  exact metricPullback_smoothOn g (coordinateDomain_open p) (coordinateInverse_smoothOn p) _ _

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



theorem coordinateMetric_ball_bounds (g : SmoothMetric M) (p : M) {r : ℝ}
    (hball : Metric.closedBall (coordinateCenter p) r ⊆ coordinateDomain p) :
    let U := Metric.ball (coordinateCenter p) r
    let T := coordinateMetric g p '' Metric.closedBall (coordinateCenter p) r
    IsCompact T ∧ (∀ H ∈ T, 0 < H 0) ∧ (∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) ∧
      (∀ x ∈ U, coordinateMetric g p x ∈ T) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ U, ∀ y ∈ U,
        ‖coordinateMetric g p y-coordinateMetric g p x‖ ≤ L*‖y-x‖ := by
  dsimp only
  obtain ⟨hT,hT0,hTd⟩ := coordinateMetric_compact_positive g p
    (isCompact_closedBall (coordinateCenter p) r) hball
  refine ⟨hT,hT0,hTd,fun x hx => ⟨x,Metric.ball_subset_closedBall hx,rfl⟩,?_⟩
  have hc := (coordinateMetric_smoothOn g p).continuousOn_fderiv_of_isOpen
    (coordinateDomain_open p) (by simp)
  obtain ⟨L,hL⟩ := (isCompact_closedBall (coordinateCenter p) r).exists_bound_of_continuousOn
    (hc.mono hball)
  refine ⟨max 0 L,le_max_left _ _,fun x hx y hy => ?_⟩
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _ (convex_ball _ _) hx hy
  · intro a ha
    exact (((coordinateMetric_smoothOn g p) a (hball (Metric.ball_subset_closedBall ha))).contDiffAt
      ((coordinateDomain_open p).mem_nhds (hball (Metric.ball_subset_closedBall ha)))).differentiableAt
      (by simp)
  · intro a ha
    exact (hL a (Metric.ball_subset_closedBall ha)).trans (le_max_right _ _)

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



theorem finite_atlas_metric_bounds {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) (p : ι → M) (r : ι → ℝ)
    (hball : ∀ i, Metric.closedBall (coordinateCenter (p i)) (r i) ⊆ coordinateDomain (p i)) :
    ∃ T : Set PhaseMean.Tensor, ∃ L : ℝ,
      IsCompact T ∧ (∀ H ∈ T, 0 < H 0) ∧ (∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) ∧ 0 ≤ L ∧
      (∀ i x, x ∈ Metric.ball (coordinateCenter (p i)) (r i) → coordinateMetric g (p i) x ∈ T) ∧
      (∀ i x, x ∈ Metric.ball (coordinateCenter (p i)) (r i) → ∀ y,
        y ∈ Metric.ball (coordinateCenter (p i)) (r i) →
        ‖coordinateMetric g (p i) y-coordinateMetric g (p i) x‖ ≤ L*‖y-x‖) := by
  classical
  have hb (i : ι) := coordinateMetric_ball_bounds g (p i) (hball i)
  choose L hL hLip using fun i => (hb i).2.2.2.2
  let T : Set PhaseMean.Tensor := ⋃ i, coordinateMetric g (p i) '' Metric.closedBall (coordinateCenter (p i)) (r i)
  refine ⟨T,∑ i, L i,?_,?_,?_,Finset.sum_nonneg (fun i _ => hL i),?_,?_⟩
  · exact isCompact_iUnion (fun i => (hb i).1)
  · intro H hH
    obtain ⟨i,hi⟩ := mem_iUnion.mp hH
    exact (hb i).2.1 H hi
  · intro H hH
    obtain ⟨i,hi⟩ := mem_iUnion.mp hH
    exact (hb i).2.2.1 H hi
  · intro i x hx
    exact mem_iUnion.mpr ⟨i,(hb i).2.2.2.1 x hx⟩
  · intro i x hx y hy
    apply (hLip i x hx y hy).trans
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ i)) (norm_nonneg _)

end ClosedSurfaceR4

end

end OAI
