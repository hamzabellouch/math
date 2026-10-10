import Mathlib
import OAI.Analysis.SymmetricDomains.EventualOffsetBall

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter
open scoped Topology NNReal

theorem dense_lipschitz_test_limits {I E : Type*} [PseudoMetricSpace E]
    (F : I → E → ℝ) {l : Filter I} [l.NeBot] {L : ℝ≥0}
    (hL : ∀ i, LipschitzWith L (F i)) {D : Set E} (hD : Dense D)
    (htest : ∀ x ∈ D, ∃ a : ℝ, Tendsto (fun i => F i x) l (𝓝 a)) :
    ∃ f : E → ℝ, LipschitzWith L f ∧
      (∀ x, Tendsto (fun i => F i x) l (𝓝 (f x))) ∧
      ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K := by
  let g : E → ℝ := fun x => limUnder l (fun i => F i x)
  have hpt (x : E) (hx : x ∈ D) : Tendsto (fun i => F i x) l (𝓝 (g x)) := by
    obtain ⟨a,ha⟩ := htest x hx
    have he : g x = a := ha.limUnder_eq
    rwa [he]
  have hg : LipschitzOnWith L g D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hpt x hx).dist (hpt y hy))
      (Eventually.of_forall fun i => (hL i).dist_le_mul x y)
  obtain ⟨f,hf,he⟩ := hg.extend_real
  have heq : Equicontinuous F := (LipschitzWith.uniformEquicontinuous F L hL).equicontinuous
  have hall (x : E) : Tendsto (fun i => F i x) l (𝓝 (f x)) := by
    exact (heq x).tendsto_of_mem_closure
      (hf.continuous.continuousAt.mono_left nhdsWithin_le_nhds)
      (fun y hy => by simpa only [he hy] using hpt y hy) (hD x)
  refine ⟨f,hf,hall,?_⟩
  intro K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hKlip (i : I) : LipschitzWith L (fun x : K => F i x) :=
    by simpa only [mul_one, Function.comp_def] using (hL i).comp (isometry_subtype_coe.lipschitzWith)
  have hKeq := (LipschitzWith.uniformEquicontinuous
    (fun i : I => fun x : K => F i x) L hKlip).equicontinuous
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (hKeq.tendsto_uniformFun_iff_pi l (fun x : K => f x)).mpr
  exact tendsto_pi_nhds.mpr fun x => hall x

end

open Set Filter Metric
open scoped Topology Pointwise

lemma offset_complement_dilation {S E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (offsetScaled A s t)ᶜ = c • (offsetScaled A s (c*t))ᶜ := by
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ • x,?_,smul_inv_smul₀ hc x⟩
    change (c*t) • (c⁻¹ • x) ∉ A s
    have he : (c*t)*c⁻¹ = t := by field_simp
    change t • x ∉ A s at hx
    simpa only [smul_smul,he] using hx
  · rintro ⟨y,hy,rfl⟩
    change t • (c • y) ∉ A s
    simpa only [offsetScaled,mem_ofPred_eq,mem_compl_iff,smul_smul,mul_comm t c] using hy

lemma offset_distance_dilation {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) {c : ℝ} (hc : 0 < c) (v : E) :
    infDist (c • v) (offsetScaled A s t)ᶜ = c * infDist v (offsetScaled A s (c*t))ᶜ := by
  rw [offset_complement_dilation A s t hc.ne',infDist_smul₀ hc.ne',Real.norm_eq_abs,abs_of_pos hc]

theorem offset_limit_zero_cone {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) {f : E → ℝ}
    (hf : ∀ v, Tendsto (fun t => offsetDistance A s t v) (𝓝[>] (0 : ℝ)) (𝓝 (f v)))
    (v : E) {c : ℝ} (hc : 0 < c) : f v = 0 ↔ f (c • v) = 0 := by
  have step (v : E) {c : ℝ} (hc : 0 < c) (hv : f v = 0) : f (c • v) = 0 := by
    have hct : Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,?_⟩
      · simpa only [mul_zero] using
          (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
            Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝 (c*0)))
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos hc ht
    have hzero : Tendsto (fun t => offsetDistance A s (c*t) v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Function.comp_def,hv] using (hf v).comp hct
    have hraw : Tendsto (fun t => infDist v (offsetScaled A s (c*t))ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_of_truncated_zero hzero
    have hraw' : Tendsto (fun t => infDist (c • v) (offsetScaled A s t)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [offset_distance_dilation A s _ hc,mul_zero] using hraw.const_mul c
    have htrunc : Tendsto (fun t => offsetDistance A s t (c • v)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [offsetDistance,min_eq_right (zero_le_one : (0:ℝ) ≤ 1)] using (tendsto_const_nhds (x := (1 : ℝ))).min hraw'
    exact tendsto_nhds_unique (hf (c • v)) htrunc
  refine ⟨step v hc,fun h => ?_⟩
  simpa only [inv_smul_smul₀ hc.ne'] using step (c • v) (inv_pos.mpr hc) h

theorem offset_limit_closed_cone {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) (h0 : (0 : E) ∉ A s) {f : E → ℝ}
    (hfl : LipschitzWith 1 f)
    (hf : ∀ v, Tendsto (fun t => offsetDistance A s t v) (𝓝[>] (0 : ℝ)) (𝓝 (f v))) :
    IsClosed {v | f v = 0} ∧ (0 : E) ∈ {v | f v = 0} ∧
      ∀ c : ℝ, 0 < c → ∀ v : E, v ∈ {v | f v = 0} ↔ c • v ∈ {v | f v = 0} := by
  refine ⟨isClosed_eq hfl.continuous continuous_const,?_,fun c hc v => offset_limit_zero_cone A s hf v hc⟩
  have h : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 (f 0)) := by
    simpa only [offsetDistance_zero A s _ h0] using hf 0
  exact (tendsto_nhds_unique h tendsto_const_nhds).symm.symm

end Release061

end

end OAI
