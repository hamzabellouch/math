import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartDerivativeNeZeroTransfer
import OAI.Geometry.SmoothYau.Estimates.VaryingPatchCoefficients
import OAI.Geometry.SmoothYau.Estimates.CoefficientPerturbationTendsto

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction SchwartzMap
namespace YauCounterexamples
section JointMetricCoefficients
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M) (p : M)
variable (hq : ∀ t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))

include hq
lemma joint_metricDet (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => (metricCoefficients (q z.1) p z.2).det) (t,y) := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact hq t y hy _ _

lemma joint_metricDensity (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => Real.sqrt (metricCoefficients (q z.1) p z.2).det) (t,y) :=
  (joint_metricDet q p hq t hy).sqrt (metricCoefficients_det_pos (q t) p hy).ne'

lemma joint_metricInverse (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) (i j : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => (metricCoefficients (q z.1) p z.2)⁻¹ i j) (t,y) := by
  classical
  have hadj : ContDiffAt ℝ ∞ (fun z : ℝ × E =>
      (metricCoefficients (q z.1) p z.2).adjugate i j) (t,y) := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro k _
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffAt_const
    · exact hq t y hy _ _
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((joint_metricDet q p hq t hy).inv (metricCoefficients_det_pos (q t) p hy).ne').mul hadj

lemma joint_metricFirstCoefficient (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) (j : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => metricFirstCoefficient (q z.1) p j z.2) (t,y) := by
  have hd := joint_metricDensity q p hq t hy
  have hn := (Real.sqrt_pos.mpr (metricCoefficients_det_pos (q t) p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := joint_metricInverse q p hq t hy i j
  have hf : ContDiffAt ℝ ∞ (fun w : (ℝ × E) × E =>
      Real.sqrt (metricCoefficients (q w.1.1) p w.2).det *
      (metricCoefficients (q w.1.1) p w.2)⁻¹ i j) ((t,y),y) := by
    simpa only [Function.comp_def] using (hd.mul ha).comp ((t,y),y)
      (show ContDiffAt ℝ ∞ (fun w : (ℝ × E) × E => (w.1.1,w.2)) ((t,y),y) from
        contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hf.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const
end JointMetricCoefficients

section CutoffFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma contDiff_joint_cutoff {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {f : ℝ × E → ℂ}
    (hf : ∀ t y, y ∈ tsupport χ → ContDiffAt ℝ ∞ f (t,y)) :
    ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2 * f z) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro z hz
  have hzχ : z ∈ tsupport (fun z : ℝ × E => χ z.2) :=
    tsupport_mul_subset_left hz
  have hy : z.2 ∈ tsupport χ :=
    tsupport_comp_subset_preimage χ continuous_snd hzχ
  rw [contMDiffAt_iff_contDiffAt]
  exact (hχ.contDiffAt.comp z contDiffAt_snd).mul (hf z.1 z.2 hy)

lemma tendsto_schwartz_family (f : ℝ → 𝓢(E,ℂ))
    (hf : ContDiff ℝ ∞ (fun z : ℝ × E => f z.1 z.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ t, tsupport (f t) ⊆ K) :
    Tendsto f (𝓝 0) (𝓝 (f 0)) := by
  have h0 : (fun t => f t-f 0) 0 = 0 := sub_self _
  have hj : ContDiff ℝ ∞ (fun z : ℝ × E => (f z.1-f 0) z.2) :=
    hf.sub ((f 0).smooth'.comp contDiff_snd)
  have hs (t : ℝ) : tsupport (f t-f 0) ⊆ K := by
    exact (tsupport_sub (f t) (f 0)).trans (union_subset (hsupp t) (hsupp 0))
  have hh := tendsto_schwartz_of_common_support (fun t => f t-f 0) hj K hK hs h0
  simpa only [sub_add_cancel,zero_add] using hh.add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => f 0) (𝓝 0) (𝓝 (f 0)))
end CutoffFamily

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma metricCoefficientSchwartz_common_support (i : A.t) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    tsupport (A.metricCoefficientSchwartz i f hf) ⊆ tsupport (A.χcoord i) :=
  tsupport_mul_subset_left

omit [T2Space M] in
lemma varyingCoefficientSchwartz_a_value (q : SmoothMetric E M) (i : A.t)
    (C : A.VaryingPatchCoefficients q i) (j l : CoordIndex E) (y : E) :
    A.metricCoefficientSchwartz i (C.a j l) (C.smooth_a j l) y =
      A.χcoord i y * ((metricCoefficients q (A.p i) y)⁻¹ j l : ℂ) := by
  change A.χcoord i y * (C.a j l y : ℂ) = _
  by_cases hy : A.χcoord i y = 0
  · simp [hy]
  · rw [C.eq_a y (subset_tsupport _ hy)]

omit [T2Space M] in
lemma varyingCoefficientSchwartz_c_value (q : SmoothMetric E M) (i : A.t)
    (C : A.VaryingPatchCoefficients q i) (j : CoordIndex E) (y : E) :
    A.metricCoefficientSchwartz i (C.c j) (C.smooth_c j) y =
      A.χcoord i y * (metricFirstCoefficient q (A.p i) j y : ℂ) := by
  change A.χcoord i y * (C.c j y : ℂ) = _
  by_cases hy : A.χcoord i y = 0
  · simp [hy]
  · rw [C.eq_c y (subset_tsupport _ hy)]

omit [T2Space M] in
theorem smoothFamily_varyingLaplacian_tendsto (q : ℝ → SmoothMetric E M)
    (hq : ∀ i t y, y ∈ (chartAt E (A.p i)).target → ∀ j l,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) (A.p i) z.2 j l) (t,y))
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) :
    Tendsto (fun t => A.varyingLaplacianCLM (q t) (C t)) (𝓝 0)
      (𝓝 (A.varyingLaplacianCLM (q 0) (C 0))) := by
  apply A.varyingLaplacianCLM_tendsto q (q 0) C (C 0)
  · intro i j l
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply tendsto_schwartz_family _ _ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    simp_rw [A.varyingCoefficientSchwartz_a_value]
    apply contDiff_joint_cutoff (A.smooth_χcoord i)
    intro t y hy
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (joint_metricInverse q (A.p i) (hq i) t (A.χcoord_target i hy) j l)
  · intro i j
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply tendsto_schwartz_family _ _ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    simp_rw [A.varyingCoefficientSchwartz_c_value]
    apply contDiff_joint_cutoff (A.smooth_χcoord i)
    intro t y hy
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (joint_metricFirstCoefficient q (A.p i) (hq i) t (A.χcoord_target i hy) j)
end CompactMetricAtlas
end YauCounterexamples
end

end OAI
