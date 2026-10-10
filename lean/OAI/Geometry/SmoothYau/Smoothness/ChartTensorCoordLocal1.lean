import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.HmoDualNorm
import OAI.Geometry.SmoothYau.Geometry.SymmLChartTrivialization
import OAI.Geometry.SmoothYau.Smoothness.LocalIntegrationParts

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {P E F G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure ContinuousSmoothFamilyOn (f : P → E → F) (U : Set E) : Prop where
  smooth : ∀ p x, x ∈ U → ContDiffAt ℝ ∞ (f p) x
  jets : ∀ n, ContinuousOn (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2) (univ ×ˢ U)

namespace ContinuousSmoothFamilyOn
variable {f : P → E → F} {U : Set E}
lemma value (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousOn (fun z : P × E => f z.1 z.2) (univ ×ˢ U) := by
  have hc := (continuousMultilinearCurryFin0 ℝ E F).continuous.continuousOn.comp
    (hf.jets 0) (mapsTo_univ _ _)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,iteratedFDeriv_zero_apply] using hc

lemma postcomp (hf : ContinuousSmoothFamilyOn f U) (g : F → G)
    (hg : ∀ p x, x ∈ U → ContDiffAt ℝ ∞ g (f p x)) :
    ContinuousSmoothFamilyOn (fun p x => g (f p x)) U := by
  classical
  refine ⟨fun p x hx => (hg p x hx).comp x (hf.smooth p x hx),fun n z hz => ?_⟩
  have hq : ∀ k, ContinuousWithinAt (fun z : P × E => iteratedFDeriv ℝ k g (f z.1 z.2))
      (univ ×ˢ U) z := fun k =>
    ((hg z.1 z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp_continuousWithinAt (f := fun w : P × E => f w.1 w.2) (hf.value z hz)
  have hc : ContinuousWithinAt (fun z : P × E =>
      (ftaylorSeries ℝ g (f z.1 z.2)).taylorComp (ftaylorSeries ℝ (f z.1) z.2) n)
      (univ ×ˢ U) z := by
    apply tendsto_finsetSum
    intro c _
    change ContinuousWithinAt (fun z : P × E =>
      (c.compAlongOrderedFinpartitionL ℝ E F G (iteratedFDeriv ℝ c.length g (f z.1 z.2)))
        (fun j => iteratedFDeriv ℝ (c.partSize j) (f z.1) z.2)) _ z
    exact ((c.compAlongOrderedFinpartitionL ℝ E F G).continuous.continuousAt.comp_continuousWithinAt
      (hq c.length)).eval (continuousWithinAt_pi.mpr (fun j => hf.jets (c.partSize j) z hz))
  apply hc.congr_of_eventuallyEq _ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact iteratedFDeriv_comp (hg w.1 w.2 hw.2) (hf.smooth w.1 w.2 hw.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  · exact iteratedFDeriv_comp (hg z.1 z.2 hz.2) (hf.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma prodMk {g : P → E → G} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) :
    ContinuousSmoothFamilyOn (fun p x => (f p x,g p x)) U := by
  refine ⟨fun p x hx => (hf.smooth p x hx).prodMk (hg.smooth p x hx),fun n => ?_⟩
  have hc := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => E) F G).continuous.continuousOn.comp
    ((hf.jets n).prodMk (hg.jets n)) (mapsTo_univ _ _)
  apply hc.congr
  intro z hz
  exact iteratedFDeriv_prodMk (hf.smooth z.1 z.2 hz.2) (hg.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma fderiv (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => fderiv ℝ (f p) x) U := by
  refine ⟨fun p x hx => (hf.smooth p x hx).fderiv_right (by simp),fun n => ?_⟩
  have hc := (continuousMultilinearCurryRightEquiv' ℝ n E F).continuous.continuousOn.comp
    (hf.jets (n+1)) (mapsTo_univ _ _)
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply]
  rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

lemma const (g : E → F) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) :
    ContinuousSmoothFamilyOn (fun _ : P => g) U := by
  refine ⟨fun _ => hg,fun n z hz => ?_⟩
  exact ((hg z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp_continuousWithinAt (f := Prod.snd)
    continuous_snd.continuousWithinAt

lemma scalar_const (a : P → F) (ha : Continuous a) :
    ContinuousSmoothFamilyOn (fun p (_ : E) => a p) U := by
  refine ⟨fun _ _ _ => contDiffAt_const,fun n => ?_⟩
  cases n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp (ha.comp continuous_fst) |>.continuousOn
  | succ n => simp only [iteratedFDeriv_succ_const]; exact continuousOn_const

lemma add {g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x+g p x) U :=
  (hf.prodMk hg).postcomp (fun z : F × F => z.1+z.2) (fun _ _ _ => by fun_prop)

lemma mul {f g : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x*g p x) U :=
  (hf.prodMk hg).postcomp (fun z : ℝ × ℝ => z.1*z.2) (fun _ _ _ => by fun_prop)

lemma inv {f : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hn : ∀ p x, x ∈ U → f p x ≠ 0) : ContinuousSmoothFamilyOn (fun p x => (f p x)⁻¹) U :=
  hf.postcomp (fun z : ℝ => z⁻¹) (fun p x hx => contDiffAt_id.inv (hn p x hx))

lemma sqrt {f : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hn : ∀ p x, x ∈ U → f p x ≠ 0) : ContinuousSmoothFamilyOn (fun p x => Real.sqrt (f p x)) U :=
  hf.postcomp Real.sqrt (fun p x hx => contDiffAt_id.sqrt (hn p x hx))
end ContinuousSmoothFamilyOn
end


section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)
lemma compactSmooth_uniformity_countable : IsCountablyGenerated (uniformity 𝓓_{K}(E,F)) := by
  rw [← (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
    (𝕜:=ℝ) (n:=⊤) (K:=K) (F:=F)).toIsUniformInducing.comap_uniformity]
  infer_instance
lemma compactSmooth_t2 : T2Space 𝓓_{K}(E,F) := by
  let : MetricSpace (E →ᵇ (E [×0]→L[ℝ] F)) := inferInstance
  apply T2Space.of_injective_continuous
    (f := (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0 : 𝓓_{K}(E,F) → E →ᵇ (E [×0]→L[ℝ] F)))
  · exact ContDiffMapSupportedIn.structureMapCLM_zero_injective ℝ
  · exact (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0).continuous

@[instance_reducible] def compactSmoothMetricSpace : MetricSpace 𝓓_{K}(E,F) := by
  letI := compactSmooth_uniformity_countable (F:=F) K
  letI := compactSmooth_t2 (F:=F) K
  exact UniformSpace.metricSpace _
lemma compactSmooth_continuousJets (n : ℕ) : Continuous
    (fun z : 𝓓_{K}(E,F) × E => iteratedFDeriv ℝ n z.1 z.2) := by
  have hc := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n).continuous.comp
    (continuous_fst : Continuous (Prod.fst : 𝓓_{K}(E,F) × E → 𝓓_{K}(E,F)))).eval continuous_snd
  change Continuous (fun z : 𝓓_{K}(E,F) × E =>
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n z.1) z.2) at hc
  simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using hc
lemma compactSmooth_family : ContinuousSmoothFamilyOn (fun f : 𝓓_{K}(E,F) => (f:E→F)) univ :=
  ⟨fun f _ _ => f.contDiff.contDiffAt,fun n => (compactSmooth_continuousJets K n).continuousOn⟩

end


section
open Set Filter Function Manifold
open scoped Topology ContDiff SchwartzMap
namespace ContinuousSmoothFamilyOn
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E}
lemma sum {ι : Type*} (s : Finset ι) (f : ι → P → E → F)
    (hf : ∀ i ∈ s, ContinuousSmoothFamilyOn (f i) U) :
    ContinuousSmoothFamilyOn (fun p x => ∑ i ∈ s, f i p x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalar_const (P:=P) (E:=E) (U:=U) (fun _ => (0 : F)) continuous_const
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma prod {ι : Type*} (s : Finset ι) (f : ι → P → E → ℝ)
    (hf : ∀ i ∈ s, ContinuousSmoothFamilyOn (f i) U) :
    ContinuousSmoothFamilyOn (fun p x => ∏ i ∈ s, f i p x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalar_const (P:=P) (E:=E) (U:=U) (fun _ => (1 : ℝ)) continuous_const
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma neg {f : P → E → F} (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => -f p x) U :=
  hf.postcomp (fun z : F => -z) (fun _ _ _ => contDiffAt_id.neg)
lemma sub {f g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x-g p x) U := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma mono {f : P → E → F} (hf : ContinuousSmoothFamilyOn f U) {V : Set E} (hV : V ⊆ U) :
    ContinuousSmoothFamilyOn f V :=
  ⟨fun p x hx => hf.smooth p x (hV hx),fun n => (hf.jets n).mono (prod_mono_right hV)⟩
lemma of_local {f : P → E → F}
    (hf : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ContinuousSmoothFamilyOn f V) :
    ContinuousSmoothFamilyOn f U := by
  constructor
  · intro p x hx
    obtain ⟨V,hV,hxV,hfV⟩ := hf x hx
    exact hfV.smooth p x hxV
  · intro n z hz
    obtain ⟨V,hV,hzV,hfV⟩ := hf z.2 hz.2
    exact ((hfV.jets n (z) ⟨mem_univ _,hzV⟩).continuousAt
      ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _,hzV⟩)).continuousWithinAt
lemma congr {f g : P → E → F} (hU : IsOpen U) (hf : ContinuousSmoothFamilyOn f U)
    (he : ∀ p, EqOn (g p) (f p) U) : ContinuousSmoothFamilyOn g U := by
  have heq (p : P) (x : E) (hx : x ∈ U) : g p =ᶠ[𝓝 x] f p :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,he p⟩
  refine ⟨fun p x hx => (hf.smooth p x hx).congr_of_eventuallyEq (heq p x hx),fun n => ?_⟩
  apply (hf.jets n).congr
  intro z hz
  exact ((heq z.1 z.2 hz.2).iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
end ContinuousSmoothFamilyOn

section MetricFamily
variable {P E M : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : P → SmoothMetric E M) (p : M)
variable (hq : ∀ i j, ContinuousSmoothFamilyOn (fun t y => metricCoefficients (q t) p y i j) (chartAt E p).target)
include hq
lemma family_metricDet : ContinuousSmoothFamilyOn
    (fun t y => (metricCoefficients (q t) p y).det) (chartAt E p).target := by
  classical
  simp only [Matrix.det_apply']
  apply ContinuousSmoothFamilyOn.sum
  intro σ _
  apply (ContinuousSmoothFamilyOn.scalar_const _ continuous_const).mul
  apply ContinuousSmoothFamilyOn.prod
  intro i _
  exact hq _ _
lemma family_metricDensity : ContinuousSmoothFamilyOn
    (fun t y => Real.sqrt (metricCoefficients (q t) p y).det) (chartAt E p).target :=
  (family_metricDet q p hq).sqrt (fun t _ hy => (metricCoefficients_det_pos (q t) p hy).ne')
lemma family_metricInverse (i j : CoordIndex E) : ContinuousSmoothFamilyOn
    (fun t y => (metricCoefficients (q t) p y)⁻¹ i j) (chartAt E p).target := by
  classical
  have hadj : ContinuousSmoothFamilyOn (fun t y => (metricCoefficients (q t) p y).adjugate i j)
      (chartAt E p).target := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContinuousSmoothFamilyOn.sum
    intro σ _
    apply (ContinuousSmoothFamilyOn.scalar_const _ continuous_const).mul
    apply ContinuousSmoothFamilyOn.prod
    intro k _
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact ContinuousSmoothFamilyOn.scalar_const _ continuous_const
    · exact hq _ _
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((family_metricDet q p hq).inv (fun t y hy => (metricCoefficients_det_pos (q t) p hy).ne')).mul hadj
lemma family_metricFirstCoefficient (j : CoordIndex E) : ContinuousSmoothFamilyOn
    (fun t y => metricFirstCoefficient (q t) p j y) (chartAt E p).target := by
  apply ((family_metricDensity q p hq).inv
    (fun t y hy => (Real.sqrt_pos.mpr (metricCoefficients_det_pos (q t) p hy)).ne')).mul
  apply ContinuousSmoothFamilyOn.sum
  intro i _
  exact (((family_metricDensity q p hq).mul (family_metricInverse q p hq i j)).fderiv).postcomp
    (fun L : E →L[ℝ] ℝ => L (Module.finBasis ℝ E i)) (fun _ _ _ => by fun_prop)
end MetricFamily

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem continuous_schwartz_common_support (f : P → 𝓢(E,F))
    (hf : ∀ n, Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ t, tsupport (f t) ⊆ K) : Continuous f := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt,(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k,n⟩ ε hε
  have hj : Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f t₀) z.2) := by
    have he : (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f t₀) z.2) =
        (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2-iteratedFDeriv ℝ n (f t₀) z.2) := by
      funext z
      exact iteratedFDeriv_sub_apply
        ((f z.1).smooth'.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
        ((f t₀).smooth'.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    rw [he]
    exact (hf n).sub (((f t₀).smooth'.continuous_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp continuous_snd)
  have hc : Continuous (fun z : P × E => ‖z.2‖^k*‖iteratedFDeriv ℝ n (f z.1-f t₀) z.2‖) :=
    (continuous_snd.norm.pow k).mul hj.norm
  have he : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K,
      ‖x‖^k*‖iteratedFDeriv ℝ n (f t-f t₀) x‖ < ε/2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hzero : ‖x‖^k*‖iteratedFDeriv ℝ n (f t₀-f t₀) x‖ = 0 := by simp
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa only [hzero] using half_pos hε))
  filter_upwards [he] with t ht
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (f t-f t₀) (by positivity) ?_) (half_lt_self hε)
  intro x
  by_cases hx : x ∈ K
  · exact (ht x hx).le
  · have hz : iteratedFDeriv ℝ n (f t-f t₀) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      have hs := (tsupport_sub (f t) (f t₀)).trans (union_subset (hsupp t) (hsupp t₀))
      exact hx (hs (tsupport_iteratedFDeriv_subset n hh))
    simp only [hz,norm_zero,mul_zero]
    positivity
end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
local instance (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := ContinuousLinearMap.isTopologicalAddGroup
local instance (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance

def chartTrivMetricForm (g : SmoothMetric E M) (p : M) (y : E) : MetricForm E :=
  (chartFormTrivialization (E:=E) p ⟨(chartAt E p).symm y,g.inner ((chartAt E p).symm y)⟩).2

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffAt_chartTrivMetricForm (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : ContDiffAt ℝ ∞ (chartTrivMetricForm g p) y := by
  let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
    fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
  have hx : (chartAt E p).symm y ∈ (chartFormTrivialization (E:=E) p).baseSet := by
    rw [chartFormTrivialization_baseSet]
    exact (chartAt E p).map_target hy
  have hg := ((chartFormTrivialization (E:=E) p).contMDiffAt_section_iff hx).mp
    (g.contMDiff ((chartAt E p).symm y))
  exact contMDiffAt_iff_contDiffAt.mp (hg.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartTrivMetricForm_pairing (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (v w : E) :
    chartTrivMetricForm g p y v w = g.inner ((chartAt E p).symm y)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm ((chartAt E p).symm y) v)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm ((chartAt E p).symm y) w) :=
  chartFormTrivialization_pairing p ((chartAt E p).map_target hy) _ _ _

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartTrivMetricForm_pos (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (v : E) (hv : v ≠ 0) :
    0 < chartTrivMetricForm g p y v v := by
  rw [chartTrivMetricForm_pairing g p hy]
  have hx : (chartAt E p).symm y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using (chartAt E p).map_target hy
  let e := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).continuousLinearEquivAt ℝ _ hx
  apply g.pos
  change e.symm v ≠ 0
  simpa only [ne_eq,EmbeddingLike.map_eq_zero_iff] using hv

variable (g : SmoothMetric E M) (p : M) (K : Compacts E)

def chartTensorPositive (H : 𝓓_{K}(E,MetricForm E)) : Prop :=
  ∀ y ∈ (K : Set E), positiveFormOn (⊤ : Submodule ℝ E)
    (chartTrivMetricForm g p y + symmetrizeMetricForm (H y))

omit [T2Space M] in
lemma chartTensorPositive_zero (hK : (K : Set E) ⊆ (chartAt E p).target) :
    chartTensorPositive g p K 0 := by
  intro y hy v _ hv
  simpa only [FunLike.coe_zero,Pi.zero_apply,map_zero,add_zero] using
    chartTrivMetricForm_pos g p (hK hy) v hv

omit [T2Space M] in
lemma isOpen_chartTensorPositive (hK : (K : Set E) ⊆ (chartAt E p).target) :
    IsOpen {H : 𝓓_{K}(E,MetricForm E) | chartTensorPositive g p K H} := by
  rw [isOpen_iff_mem_nhds]
  intro H hH
  apply K.isCompact.eventually_forall_of_forall_eventually
  intro y hy
  have hEval : Continuous (fun z : 𝓓_{K}(E,MetricForm E) × E => z.1 z.2) := by
    simpa only [univ_prod_univ,continuousOn_univ] using (compactSmooth_family (F:=MetricForm E) K).value
  have h₁ : ContinuousAt (fun z : 𝓓_{K}(E,MetricForm E) × E => chartTrivMetricForm g p z.2) (H,y) :=
    ContinuousAt.comp (f := Prod.snd) (g := chartTrivMetricForm g p) (x := (H,y))
      (contDiffAt_chartTrivMetricForm g p (hK hy)).continuousAt continuous_snd.continuousAt
  have h₂ : Continuous (fun z : 𝓓_{K}(E,MetricForm E) × E => symmetrizeMetricForm (z.1 z.2)) :=
    (symmetrizeMetricForm (E:=E)).continuous.comp hEval
  have hc := h₁.add h₂.continuousAt
  exact hc.eventually ((isOpen_positiveFormOn (⊤ : Submodule ℝ E)).mem_nhds (hH y hy))

omit [T2Space M] in
lemma chartTensorForm_pos (hK : (K : Set E) ⊆ (chartAt E p).target)
    (H : 𝓓_{K}(E,MetricForm E)) (hH : chartTensorPositive g p K H)
    (x : M) (v : TangentSpace 𝓘(ℝ,E) x) (hv : v ≠ 0) :
    0 < (g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x) v v := by
  by_cases hx : x ∈ (chartAt E p).source
  · by_cases hy : (chartAt E p) x ∈ (K : Set E)
    · have hx' : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
        simpa only [TangentBundle.trivializationAt_baseSet] using hx
      let e := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).continuousLinearEquivAt ℝ x hx'
      have hne : e v ≠ 0 := by simpa only [ne_eq,EmbeddingLike.map_eq_zero_iff] using hv
      have hh := hH _ hy (e v) (Submodule.mem_top) hne
      have hr : chartTrivMetricForm g p ((chartAt E p) x) (e v) (e v) = g.inner x v v := by
        rw [chartTrivMetricForm_pairing g p (hK hy),(chartAt E p).left_inv hx]
        change g.inner x (e.symm (e v)) (e.symm (e v)) = _
        rw [e.symm_apply_apply]
      change 0 < g.inner x v v + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x v v
      rw [chartFormPush_pairing p hx]
      change 0 < chartTrivMetricForm g p ((chartAt E p) x) (e v) (e v) +
        symmetrizeMetricForm (H ((chartAt E p) x)) (e v) (e v) at hh
      rw [hr] at hh
      simpa only [e,Trivialization.continuousLinearEquivAt_apply] using hh
    · have hz : chartFormPush p (fun y => symmetrizeMetricForm (H y)) x = 0 := by
        apply chartFormPush_zero
        simp [manifoldChartPush,hx,H.zero_on_compl hy]
      rw [hz]
      change 0 < g.inner x v v + (0 : ℝ)
      simpa only [add_zero] using g.pos x v hv
  · rw [chartFormPush_eq_zero_of_not_source p hx]
    change 0 < g.inner x v v + (0 : ℝ)
    simpa only [add_zero] using g.pos x v hv

def chartTensorMetric (hK : (K : Set E) ⊆ (chartAt E p).target)
    (H : 𝓓_{K}(E,MetricForm E)) (hH : chartTensorPositive g p K H) : SmoothMetric E M where
  inner x := g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x
  symm x v w := by
    change g.inner x v w + _ = g.inner x w v + _
    rw [g.symm x v w]
    congr 1
    exact chartFormPush_symm p (fun y => symmetrizeMetricForm_symm (H y)) x v w
  pos := chartTensorForm_pos g p K hK H hH
  isVonNBounded x := positive_bilinear_bounded (show E →L[ℝ] E →L[ℝ] ℝ from
    g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H y)) x)
    (chartTensorForm_pos g p K hK H hH x)
  contMDiff := by
    let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
      fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
    apply g.contMDiff.add_section
    apply contMDiff_chartFormPush
    · exact symmetrizeMetricForm.contDiff.comp H.contDiff
    · exact H.hasCompactSupport.comp_left (by simp)
    · exact (tsupport_comp_subset (g := symmetrizeMetricForm) symmetrizeMetricForm.map_zero H).trans (H.tsupport_subset.trans hK)
end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

variable (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
variable (ht : (chartAt E p).target = univ)

def chartTensorOfMetric (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) : 𝓓_{K}(E,MetricForm E) :=
  ⟨fun y => chartMetricForm g p y-chartMetricForm g₀ p y,
    contDiff_iff_contDiffAt.mpr (fun y =>
      ((chartMetricForm_contDiffOn g p).contDiffAt (by rw [ht]; exact univ_mem)).sub
        ((chartMetricForm_contDiffOn g₀ p).contDiffAt (by rw [ht]; exact univ_mem))),by
      intro y hy
      have hx : (chartAt E p).symm y ∉ (chartAt E p).symm '' (K : Set E) := by
        rintro ⟨z,hz,heq⟩
        have hyt : y ∈ (chartAt E p).target := ht ▸ mem_univ y
        have hzt : z ∈ (chartAt E p).target := ht ▸ mem_univ z
        have hz' : z=y := by
          simpa only [(chartAt E p).right_inv hyt,(chartAt E p).right_inv hzt]
            using (congrArg (chartAt E p) heq)
        exact hy (hz' ▸ hz)
      ext v w
      simp only [sub_apply,chartMetricForm_pairing,he _ hx,sub_self,Pi.zero_apply,zero_apply]⟩

omit [T2Space M] in
lemma chartTensorOfMetric_isSymm (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) (y : E) :
    symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y) = chartTensorOfMetric g₀ p K ht g he y := by
  apply symmetrizeMetricForm_eq_self
  intro v w
  change chartMetricForm g p y v w-chartMetricForm g₀ p y v w = _
  rw [chartMetricForm_symm g p y v w,chartMetricForm_symm g₀ p y v w]
  rfl

omit [T2Space M] in
lemma chartTensorOfMetric_positive (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) :
    chartTensorPositive g₀ p K (chartTensorOfMetric g₀ p K ht g he) := by
  intro y hy v _ hv
  rw [chartTensorOfMetric_isSymm]
  change 0 < (chartTrivMetricForm g₀ p y + (chartMetricForm g p y-chartMetricForm g₀ p y)) v v
  rw [show chartTrivMetricForm g₀ p y = chartMetricForm g₀ p y from
    chartFormTrivialization_metric g₀ p (ht ▸ mem_univ y),← add_sub_assoc,add_sub_cancel_left]
  exact chartMetricForm_pos g p (ht ▸ mem_univ y) hv

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma smoothMetric_ext {g h : SmoothMetric E M}
    (he : ∀ x v w, g.inner x v w = h.inner x v w) : g=h := by
  have hi : g.inner=h.inner := funext (fun x => ContinuousLinearMap.ext (fun v =>
    ContinuousLinearMap.ext (fun w => he x v w)))
  cases g
  cases h
  cases hi
  rfl

lemma chartTensorMetric_ofMetric (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) :
    chartTensorMetric g₀ p K (ht ▸ subset_univ _) (chartTensorOfMetric g₀ p K ht g he)
      (chartTensorOfMetric_positive g₀ p K ht g he) = g := by
  apply smoothMetric_ext
  intro x v w
  by_cases hx : x ∈ (chartAt E p).source
  · change g₀.inner x v w + chartFormPush p (fun y =>
      symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y)) x v w = _
    rw [chartFormPush_pairing p hx]
    rw [chartTensorOfMetric_isSymm]
    change g₀.inner x v w + (chartMetricForm g p ((chartAt E p) x) -
      chartMetricForm g₀ p ((chartAt E p) x)) _ _ = _
    have hxy : (chartAt E p).symm ((chartAt E p) x) = x := (chartAt E p).left_inv hx
    have htxy := (chartAt E p).map_source hx
    rw [← chartFormTrivialization_metric g p htxy,← chartFormTrivialization_metric g₀ p htxy]
    rw [hxy]
    rw [sub_apply,sub_apply,chartFormTrivialization_pairing p hx,chartFormTrivialization_pairing p hx]
    have hx' : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hx
    simp only [Trivialization.symm_apply_apply_mk _ hx']
    ring
  · have hn : x ∉ (chartAt E p).symm '' (K : Set E) := by
      rintro ⟨y,hy,rfl⟩
      exact hx ((chartAt E p).map_target (ht ▸ mem_univ y))
    change g₀.inner x v w + chartFormPush p (fun y =>
      symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y)) x v w = _
    rw [chartFormPush_eq_zero_of_not_source p hx]
    simp only [zero_apply,add_zero,← he x hn]
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
section ChartTensorCoordinate
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance chartTensorCoordLocal1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal3 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorCoordLocal4 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorCoordLocal5 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance chartTensorCoordLocal6 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal7 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := ContinuousLinearMap.isTopologicalAddGroup
local instance chartTensorCoordLocal8 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance

lemma chartMetricForm_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : 𝓓_{K}(E,MetricForm E))
    (hH : chartTensorPositive g p K H) {y : E} (hy : y ∈ (chartAt E p).target) :
    chartMetricForm (chartTensorMetric g p K hK H hH) p y =
      chartMetricForm g p y + symmetrizeMetricForm (H y) := by
  rw [← chartFormTrivialization_metric _ p hy,← chartFormTrivialization_metric g p hy]
  ext v w
  rw [chartFormTrivialization_pairing p ((chartAt E p).map_target hy),add_apply,add_apply,
    chartFormTrivialization_pairing p ((chartAt E p).map_target hy)]
  change g.inner _ _ _ + chartFormPush p (fun y => symmetrizeMetricForm (H y)) _ _ _ = _
  congr 1
  rw [← chartFormTrivialization_pairing p ((chartAt E p).map_target hy),
    chartFormPush_trivialization p ((chartAt E p).map_target hy),(chartAt E p).right_inv hy]

lemma metricCoefficient_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : 𝓓_{K}(E,MetricForm E))
    (hH : chartTensorPositive g p K H) {y : E} (hy : y ∈ (chartAt E p).target)
    (i j : CoordIndex E) :
    metricCoefficients (chartTensorMetric g p K hK H hH) p y i j =
      metricCoefficients g p y i j + symmetrizeMetricForm (H y)
        (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  have h := congrArg (fun B : MetricForm E => B (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
    (chartMetricForm_chartTensorMetric g p K hK H hH hy)
  simpa only [add_apply,chartMetricForm_pairing,metricCoefficients,coordinateVector] using h

variable {P : Type*} [TopologicalSpace P]
lemma family_chartTensorMetric_main (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : P → 𝓓_{K}(E,MetricForm E))
    (hH : ∀ a, chartTensorPositive g p K (H a)) (hc : Continuous H) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (chartTensorMetric g p K hK (H a) (hH a)) p y i j)
      (chartAt E p).target := by
  have hfamily := compactSmooth_family (F:=MetricForm E) K
  have hparam : ContinuousSmoothFamilyOn (fun a => (H a : E → MetricForm E)) univ := by
    refine ⟨fun a => hfamily.smooth (H a),fun degree => ?_⟩
    exact (hfamily.jets degree).comp ((hc.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun pair hpair => ⟨mem_univ _,hpair.2⟩)
  have hf := hparam.postcomp
    (fun B : MetricForm E => symmetrizeMetricForm B (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
    (fun _ _ _ => by fun_prop)
  have hb := ContinuousSmoothFamilyOn.const (P:=P) (fun y => metricCoefficients g p y i j)
    (fun y hy => (contDiffOn_metricCoefficient g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy))
  apply (hb.add (hf.mono (subset_univ _))).congr (chartAt E p).open_target
  intro a y hy
  exact metricCoefficient_chartTensorMetric g p K hK (H a) (hH a) hy i j
end ChartTensorCoordinate

variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

local instance chartTensorCoordLocal9 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal10 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal11 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorCoordLocal12 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorCoordLocal13 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance chartTensorCoordLocal14 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal15 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := ContinuousLinearMap.isTopologicalAddGroup
local instance chartTensorCoordLocal16 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance

omit [T2Space M] in
lemma continuousSmoothFamily_from_chart (q : P → SmoothMetric E M) (g : SmoothMetric E M)
    (p : M) (S : Set M) (hS : IsClosed S) (hSp : S ⊆ (chartAt E p).source)
    (hq : ∀ i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y i j) (chartAt E p).target)
    (he : ∀ a x, x ∉ S → (q a).inner x = g.inner x) (r : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target := by
  classical
  apply ContinuousSmoothFamilyOn.of_local
  intro y hy
  by_cases hp : (chartAt E r).symm y ∈ (chartAt E p).source
  · obtain ⟨V,hV,hVo,hyV⟩ := mem_nhds_iff.mp (chart_overlap_nhds p r hy hp)
    have ht : ∀ z ∈ V, ContDiffAt ℝ ∞ (chartTransition p r) z :=
      fun z hz => contDiffAt_chartTransition p r (hV hz).1 (hV hz).2
    have hf (k l : CoordIndex E) : ContinuousSmoothFamilyOn
        (fun a z => metricCoefficients (q a) p (chartTransition p r z) k l) V := by
      have hmap : MapsTo (chartTransition p r) V (chartAt E p).target :=
        fun point hpoint => (chartAt E p).map_source (hV hpoint).2
      refine ⟨fun param point hpoint =>
        ((hq k l).smooth param _ (hmap hpoint)).comp point (ht point hpoint),
        fun degree pair hpair => ?_⟩
      have htransition : ContinuousOn (chartTransition p r) V :=
        fun point hpoint => (ht point hpoint).continuousAt.continuousWithinAt
      have hcomp : ContinuousOn (fun pair : P × E => (pair.1,chartTransition p r pair.2))
          (univ ×ˢ V) := continuousOn_fst.prodMk
        (htransition.comp continuousOn_snd (fun point hpoint => hpoint.2))
      have houter (order : ℕ) : ContinuousWithinAt
          (fun pair : P × E => iteratedFDeriv ℝ order
            (fun point => metricCoefficients (q pair.1) p point k l) (chartTransition p r pair.2))
          (univ ×ˢ V) pair :=
        (((hq k l).jets order).comp hcomp
          (fun point hpoint => ⟨mem_univ _,hmap hpoint.2⟩)) pair hpair
      have hinner (order : ℕ) : ContinuousWithinAt
          (fun pair : P × E => iteratedFDeriv ℝ order (chartTransition p r) pair.2)
          (univ ×ˢ V) pair :=
        ((ht pair.2 hpair.2).continuousAt_iteratedFDeriv
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl order)).comp_continuousWithinAt
          continuous_snd.continuousWithinAt
      have hjet : ContinuousWithinAt (fun pair : P × E =>
          (ftaylorSeries ℝ (fun point => metricCoefficients (q pair.1) p point k l)
            (chartTransition p r pair.2)).taylorComp (ftaylorSeries ℝ (chartTransition p r) pair.2)
            degree) (univ ×ˢ V) pair := by
        apply tendsto_finsetSum
        intro partition _
        change ContinuousWithinAt (fun pair : P × E =>
          (partition.compAlongOrderedFinpartitionL ℝ E E ℝ
            (iteratedFDeriv ℝ partition.length
              (fun point => metricCoefficients (q pair.1) p point k l) (chartTransition p r pair.2)))
            (fun index => iteratedFDeriv ℝ (partition.partSize index) (chartTransition p r) pair.2)) _ pair
        exact ((partition.compAlongOrderedFinpartitionL ℝ E E ℝ).continuous.continuousAt.comp_continuousWithinAt
          (houter partition.length)).eval
            (continuousWithinAt_pi.mpr (fun index => hinner (partition.partSize index)))
      apply hjet.congr_of_eventuallyEq _ ?_
      · filter_upwards [self_mem_nhdsWithin] with point hpoint
        exact iteratedFDeriv_comp ((hq k l).smooth point.1 _ (hmap hpoint.2)) (ht point.2 hpoint.2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl degree)
      · exact iteratedFDeriv_comp ((hq k l).smooth pair.1 _ (hmap hpair.2)) (ht pair.2 hpair.2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl degree)
    have hT (k l : CoordIndex E) : ContinuousSmoothFamilyOn
        (fun _ : P => fun z => coordinateTransitionMatrix p r z k l) V := by
      apply ContinuousSmoothFamilyOn.const
      intro z hz
      simp only [coordinateTransitionMatrix,LinearMap.toMatrix_apply]
      change ContDiffAt ℝ ∞ (fun z => (Module.finBasis ℝ E).repr
        ((fderiv ℝ (chartTransition p r) z) (Module.finBasis ℝ E l)) k) z
      exact ((Module.finBasis ℝ E).coord k).toContinuousLinearMap.contDiff.contDiffAt.comp z
        (((ht z hz).fderiv_right (by simp)).clm_apply contDiffAt_const)
    have htensor := ContinuousSmoothFamilyOn.sum Finset.univ (fun l => fun a z =>
        (∑ k, coordinateTransitionMatrix p r z k i *
          metricCoefficients (q a) p (chartTransition p r z) k l) * coordinateTransitionMatrix p r z l j)
      (fun l _ => (ContinuousSmoothFamilyOn.sum Finset.univ _
        (fun k _ => (hT k i).mul (hf k l))).mul (hT l j))
    refine ⟨V,hVo,hyV,htensor.congr hVo ?_⟩
    intro a z hz
    exact congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_change (q a) p r (hV hz).1 (hV hz).2)
  · have hn : (chartAt E r).symm y ∉ S := fun hn => hp (hSp hn)
    have hn' := ((chartAt E r).continuousAt_symm hy).eventually (hS.isOpen_compl.mem_nhds hn)
    obtain ⟨V,hV,hVo,hyV⟩ := mem_nhds_iff.mp (inter_mem ((chartAt E r).open_target.mem_nhds hy) hn')
    refine ⟨V,hVo,hyV,?_⟩
    have hf := ContinuousSmoothFamilyOn.const (P:=P) (fun z => metricCoefficients g r z i j)
      (U:=V) (fun z hz => (contDiffOn_metricCoefficient g r i j).contDiffAt
        ((chartAt E r).open_target.mem_nhds (hV hz).1))
    apply hf.congr hVo
    intro a z hz
    exact congrArg (fun B => B (coordinateVector r z i) (coordinateVector r z j))
      (he a ((chartAt E r).symm z) (hV hz).2)
lemma family_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : P → 𝓓_{K}(E,MetricForm E))
    (hH : ∀ a, chartTensorPositive g p K (H a)) (hc : Continuous H)
    (r : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (chartTensorMetric g p K hK (H a) (hH a)) r y i j)
      (chartAt E r).target := by
  apply continuousSmoothFamily_from_chart _ g p ((chartAt E p).symm '' (K : Set E))
  · exact (K.isCompact.image_of_continuousOn ((chartAt E p).continuousOn_symm.mono hK)).isClosed
  · rintro x ⟨y,hy,rfl⟩
    exact (chartAt E p).map_target (hK hy)
  · exact family_chartTensorMetric_main g p K hK H hH hc
  · intro a x hx
    change g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H a y)) x = g.inner x
    suffices hh : chartFormPush p (fun y => symmetrizeMetricForm (H a y)) x = 0 by
      rw [hh]
      ext v w
      change g.inner x v w + (0 : ℝ) = g.inner x v w
      exact add_zero _
    by_cases hxp : x ∈ (chartAt E p).source
    · apply chartFormPush_zero
      have hy : (chartAt E p) x ∉ (K : Set E) := by
        intro hy
        exact hx ⟨(chartAt E p) x,hy,(chartAt E p).left_inv hxp⟩
      simp [manifoldChartPush,hxp,(H a).zero_on_compl hy]
    · exact chartFormPush_eq_zero_of_not_source p hxp

end YauCounterexamples
end

end OAI
