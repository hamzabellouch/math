import OAI.Geometry.Relativity.CKS.SurfaceVolume
import OAI.Geometry.Relativity.CKS.SurfaceDeterminant

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma metric_nonneg (g : Metric (M := M)) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

lemma chartMatrix_posSemidef (g : Metric (M := M)) (x : M) (y : E) :
    (chartMatrix g x y).PosSemidef := by
  rw [chartMatrix_eq_toMatrix]
  apply (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp
  constructor
  · constructor
    intro v w
    exact g.symm _ _ _
  · constructor
    intro v
    exact metric_nonneg g _ _

lemma chartMatrix_sub_posSemidef (g G : Metric (M := M)) {c : ℝ}
    (hlow : ∀ x (v : TangentSpace I x), c*g.inner x v v ≤ G.inner x v v)
    (x : M) (y : E) :
    (chartMatrix G x y - c • chartMatrix g x y).PosSemidef := by
  have h : LinearMap.IsPosSemidef (pullbackInner G x y - c • pullbackInner g x y) := by
    constructor
    · constructor
      intro v w
      change G.inner _ _ _ - c*g.inner _ _ _ = G.inner _ _ _ - c*g.inner _ _ _
      exact congrArg₂ (fun a b : ℝ => a - c*b) (G.symm _ _ _) (g.symm _ _ _)
    · constructor
      intro v
      exact sub_nonneg.mpr (hlow _ _)
  have hh := (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp h
  have heq : (LinearMap.toMatrix₂ stdBasis stdBasis)
      (pullbackInner G x y - c • pullbackInner g x y) =
      chartMatrix G x y - c • chartMatrix g x y := by
    ext i j
    simp [chartMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.toMatrix₂_apply]
  rw [heq] at hh
  exact hh

lemma chartDensity_lower (g G : Metric (M := M)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x (v : TangentSpace I x), c*g.inner x v v ≤ G.inner x v v)
    (x : M) (y : E) : c * chartDensity g x y ≤ chartDensity G x y :=
  sqrt_det_two_lower _ _ (chartMatrix_posSemidef g x y) hc
    (chartMatrix_sub_posSemidef g G hlow x y)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

omit [SecondCountableTopology M] in
lemma localVolume_lower [SecondCountableTopology M] (g G : Metric (M := M)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x (v : TangentSpace I x), c*g.inner x v v ≤ G.inner x v v)
    (x : M) : ENNReal.ofReal c • localVolume g x ≤ localVolume G x := by
  apply Measure.le_iff.2
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,localVolume_apply g x hs,localVolume_apply G x hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  change ENNReal.ofReal c * ENNReal.ofReal (chartDensity g x y) ≤
    ENNReal.ofReal (chartDensity G x y)
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (chartDensity_lower g G hc hlow x y)

end CKSSurfaceVolume

end

end OAI
