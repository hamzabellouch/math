import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def scaledMetric (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x) where
  inner x := c • g.inner x
  symm x v w := congrArg (c * ·) (g.symm x v w)
  pos x v hv := mul_pos hc (g.pos x v hv)
  isVonNBounded x := CKSInducedArea.positive_bilinear_bounded (c • g.inner x)
    (fun v hv => mul_pos hc (g.pos x v hv))
  contMDiff := by
    let (x : M) : NormedAddCommGroup (TangentSpace I x) := by unfold TangentSpace; infer_instance
    let (x : M) : NormedSpace ℝ (TangentSpace I x) := by unfold TangentSpace; infer_instance
    let (x : M) : ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := by
      change ContinuousAdd (E →L[ℝ] ℝ); infer_instance
    let (x : M) : ContinuousAdd (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
      change ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ); infer_instance
    exact g.contMDiff.const_smul_section

@[simp] lemma scaledMetric_apply (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) (x : M) (v w : E) : (scaledMetric g c hc).inner x v w = c * g.inner x v w := rfl

lemma chartDensity_scaled (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) (x : M) (y : E) :
    chartDensity (scaledMetric g c hc).toContinuousRiemannianMetric x y =
      c * chartDensity g.toContinuousRiemannianMetric x y := by
  have hM : chartMatrix (scaledMetric g c hc).toContinuousRiemannianMetric x y =
      c • chartMatrix g.toContinuousRiemannianMetric x y := by ext i j; rfl
  rw [chartDensity,hM,Matrix.det_smul, Fintype.card_fin,Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq hc.le]
  rfl

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
lemma riemannianVolume_scaled (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) :
    riemannianVolume (scaledMetric g c hc).toContinuousRiemannianMetric =
      ENNReal.ofReal c • riemannianVolume g.toContinuousRiemannianMetric := by
  apply volume_unique _ (riemannianVolume_isVolume _)
  intro x
  rw [Measure.restrict_smul,(riemannianVolume_isVolume g.toContinuousRiemannianMetric) x]
  apply Measure.ext
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,localVolume_apply _ _ hs,localVolume_apply _ _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [chartDensity_scaled,ENNReal.ofReal_mul hc.le]

end CKSSurfaceVolume

end

end OAI
