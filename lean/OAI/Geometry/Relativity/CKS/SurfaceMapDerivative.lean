import OAI.Geometry.Relativity.CKS.SurfaceVolumeLower

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff
namespace CKSSurfaceVolume
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]

def mapChart (f : M → N) (x : M) (y : N) : E → E :=
  (extChartAt I y) ∘ f ∘ (extChartAt I x).symm

def mapChartDeriv (f : M → N) (x : M) (y : N) (z : E) : E →L[ℝ] E :=
  (mfderiv I I (extChartAt I y) (f ((extChartAt I x).symm z))).comp
    ((mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z))

lemma hasFDerivWithinAt_mapChart (f : M → N) (hf : ContMDiff I I 1 f)
    (x : M) (y : N) {z : E} (hz : z ∈ (extChartAt I x).target)
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    HasFDerivWithinAt (mapChart f x y) (mapChartDeriv f x y z) (range I) z := by
  exact ((mdifferentiableAt_extChartAt (by simpa using hy)).hasMFDerivAt.comp_hasMFDerivWithinAt z
    (((hf.mdifferentiable (by norm_num)) _).hasMFDerivAt.comp_hasMFDerivWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt)).hasFDerivWithinAt

lemma mapChart_frame {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
    (f : M → N) (x : M) (y : N) {z : E}
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    (chartFrame y (mapChart f x y z)).comp (mapChartDeriv f x y z) =
      (mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z) := by
  unfold mapChartDeriv
  change (mfderivWithin I I (extChartAt I y).symm (range I)
    (extChartAt I y (f ((extChartAt I x).symm z)))).comp
      ((mfderiv I I (extChartAt I y) (f ((extChartAt I x).symm z))).comp _) = _
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy]
  rfl

def mapPullbackInner (h : Metric (M := N)) (f : M → N) (x : M) (z : E) :
    LinearMap.BilinForm ℝ E :=
  (h.inner (f ((extChartAt I x).symm z))).toBilinForm.comp
    ((mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z)).toLinearMap
    ((mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z)).toLinearMap

lemma mapPullbackInner_eq (h : Metric (M := N)) (f : M → N) (x : M) (y : N) {z : E}
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    mapPullbackInner h f x z = (pullbackInner h y (mapChart f x y z)).comp
      (mapChartDeriv f x y z).toLinearMap (mapChartDeriv f x y z).toLinearMap := by
  ext v w
  change h.inner (f ((extChartAt I x).symm z))
    ((mfderiv I I f ((extChartAt I x).symm z)) (chartFrame x z v))
    ((mfderiv I I f ((extChartAt I x).symm z)) (chartFrame x z w)) =
    h.inner ((extChartAt I y).symm (mapChart f x y z))
      (chartFrame y (mapChart f x y z) (mapChartDeriv f x y z v))
      (chartFrame y (mapChart f x y z) (mapChartDeriv f x y z w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (mapChart_frame f x y hy)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (mapChart_frame f x y hy)
  change chartFrame y (mapChart f x y z) (mapChartDeriv f x y z v) = _ at hv
  change chartFrame y (mapChart f x y z) (mapChartDeriv f x y z w) = _ at hw
  rw [hv,hw]
  have heq : (extChartAt I y).symm (mapChart f x y z) = f ((extChartAt I x).symm z) :=
    (extChartAt I y).left_inv hy
  rw [heq]
  rfl

lemma mapPullbackInner_posSemidef {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
    (h : Metric (M := N)) (f : M → N) (x : M) (z : E) :
    LinearMap.IsPosSemidef (mapPullbackInner h f x z) := by
  constructor
  · constructor
    intro v w
    exact h.symm _ _ _
  · constructor
    intro v
    exact metric_nonneg h _ _

lemma mapChart_density_le (g : Metric (M := M)) (h : Metric (M := N)) (f : M → N)
    (hshort : ∀ x v, h.inner (f x) (mfderiv I I f x v) (mfderiv I I f x v) ≤ g.inner x v v)
    (x : M) (y : N) {z : E}
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    |(mapChartDeriv f x y z).det| * chartDensity h y (mapChart f x y z) ≤ chartDensity g x z := by
  have hp := (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp
    (mapPullbackInner_posSemidef h f x z)
  have hd : LinearMap.IsPosSemidef (pullbackInner g x z - mapPullbackInner h f x z) := by
    constructor
    · constructor
      intro v w
      exact congrArg₂ (fun a b : ℝ => a-b) (g.symm _ _ _) (h.symm _ _ _)
    · constructor
      intro v
      exact sub_nonneg.mpr (hshort _ _)
  have hdm := (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp hd
  have heq : LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x z - mapPullbackInner h f x z) =
      chartMatrix g x z - (1 : ℝ) • LinearMap.BilinForm.toMatrix stdBasis (mapPullbackInner h f x z) := by
    ext i j
    simp [chartMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_apply]
  change (LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x z - mapPullbackInner h f x z)).PosSemidef at hdm
  change (LinearMap.BilinForm.toMatrix stdBasis (mapPullbackInner h f x z)).PosSemidef at hp
  rw [heq] at hdm
  have hb := sqrt_det_two_lower _ _ hp (by norm_num : (0:ℝ) ≤ 1) hdm
  simpa only [one_mul,mapPullbackInner_eq h f x y hy,sqrt_gram_det_comp,
    ← chartMatrix_eq_toMatrix, chartDensity] using hb

end CKSSurfaceVolume

end

end OAI
