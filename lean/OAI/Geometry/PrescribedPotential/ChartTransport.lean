import Mathlib
import OAI.Geometry.PrescribedPotential.LocalRegularity
import OAI.Geometry.PrescribedPotential.LocalizedPullback

namespace OAI

/-! Chart Transport. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction

namespace GlobalElliptic
open SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 
structure ChartCutoff (U : Set E) where
  val : 𝓢(E, ℂ)
  compact : HasCompactSupport (val : E → ℂ)
  support_sub : tsupport (val : E → ℂ) ⊆ U

instance {U : Set E} : CoeFun (ChartCutoff U) (fun _ => E → ℂ) := ⟨fun κ => κ.val⟩

namespace ChartCutoff
variable {U : Set E} (κ : ChartCutoff U)

lemma product_smooth {h : E → ℂ} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) :
    ContDiff ℝ ∞ (fun x => κ x * h x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (κ.val.smooth ⊤).contDiffAt.mul (hh.contDiffAt (hU.mem_nhds hx))
  · have ht : x ∉ tsupport (κ : E → ℂ) := fun ht => hx (κ.support_sub ht)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
    simp [hy]

lemma product_compact (h : E → ℂ) : HasCompactSupport (fun x => κ x * h x) := by
  apply HasCompactSupport.of_support_subset_isCompact κ.compact
  intro x hx
  exact subset_tsupport _ (left_ne_zero_of_mul hx)

def product {h : E → ℂ} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) : 𝓢(E, ℂ) :=
  (κ.product_compact h).toSchwartzMap (κ.product_smooth hU hh)

@[simp] lemma product_apply {h : E → ℂ} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) (x : E) :
    κ.product hU hh x = κ x * h x := rfl

lemma product_tsupport {h : E → ℂ} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) :
    tsupport (κ.product hU hh : E → ℂ) ⊆ tsupport (κ : E → ℂ) := by
  apply closure_mono
  exact fun x hx => left_ne_zero_of_mul hx

 
def mulOn {h : E → ℂ} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) : ChartCutoff U where
  val := κ.product hU hh
  compact := κ.product_compact h
  support_sub := (κ.product_tsupport hU hh).trans κ.support_sub

lemma deriv_tsupport (v : E) :
    tsupport (⇑(∂_{v} κ.val : 𝓢(E, ℂ))) ⊆ tsupport (κ : E → ℂ) := by
  intro x hx
  by_contra hn
  have hh := notMem_tsupport_iff_eventuallyEq.mp hn
  have hd : (fun y => (∂_{v} κ.val : 𝓢(E, ℂ)) y) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hh.eventually_nhds] with y hy
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hy' : (κ : E → ℂ) =ᶠ[𝓝 y] 0 := hy
    rw [hy'.fderiv_eq]
    simp
  exact (notMem_tsupport_iff_eventuallyEq.mpr hd) hx

def deriv (v : E) : ChartCutoff U where
  val := ∂_{v} κ.val
  compact := (κ.compact.of_isClosed_subset (isClosed_tsupport _) (κ.deriv_tsupport v))
  support_sub := (κ.deriv_tsupport v).trans κ.support_sub

end ChartCutoff

variable (e : OpenPartialHomeomorph E E) (he : ContDiffOn ℝ ∞ e e.source)

 
def chartTransport (κ : ChartCutoff e.source) : 𝓢(E, ℂ) →ₗ[ℝ] 𝓢(E, ℂ) where
  toFun f := κ.product e.open_source ((f.smooth ⊤).comp_contDiffOn he)
  map_add' f h := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp [mul_left_comm]

@[simp] lemma chartTransport_apply (κ : ChartCutoff e.source) (f : 𝓢(E, ℂ)) (x : E) :
    chartTransport e he κ f x = κ x * f (e x) := rfl

 
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem chartTransport_l2_bound (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (κ : ChartCutoff e.source) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E, ℂ),
      ‖schwartzCoord 0 (chartTransport e he κ f)‖ ≤ C * ‖schwartzCoord 0 f‖ := by
  let K := tsupport (κ : E → ℂ)
  obtain ⟨C, hC, hmeas, hmap⟩ := chart_map_restrict_bound e he hs κ.compact κ.support_sub
  let B : L2 E →L[ℝ] L2 E :=
    (Lp.extendZero (μ := (volume : Measure E)) (p := 2) (F := ℂ) (isClosed_tsupport _).measurableSet).toContinuousLinearMap ∘L
      Lp.pullbackBounded (K.indicator e) hmeas ENNReal.ofReal_ne_top hmap
  let T : L2 E →L[ℝ] L2 E := (multiply κ.val.toBoundedContinuousFunction).restrictScalars ℝ ∘L B
  refine ⟨‖T‖, norm_nonneg _, fun f => ?_⟩
  have hc (u : 𝓢(E, ℂ)) : schwartzCoord 0 u = u.toLp 2 volume := by
    apply realize_injective 0
    simpa [realize] using realize_schwartzCoord 0 u
  rw [hc, hc]
  have heq : T (f.toLp 2 volume) = (chartTransport e he κ f).toLp 2 volume := by
    apply Lp.ext
    have hb := Lp.coeFn_pullbackBounded (K.indicator e) hmeas ENNReal.ofReal_ne_top hmap
      (f.toLp 2 volume)
    have hz := Lp.coeFn_extendZero (μ := (volume : Measure E))
      (isClosed_tsupport (κ : E → ℂ)).measurableSet
      (Lp.pullbackBounded (K.indicator e) hmeas ENNReal.ofReal_ne_top hmap (f.toLp 2 volume))
    have hf := (f.memLp 2 volume).coeFn_toLp
    have hfc := (ae_of_ae_map hmeas.aemeasurable
      (ae_mono hmap (Measure.ae_smul_measure hf _)))
    have ht := (chartTransport e he κ f).coeFn_toLp (p := 2) (μ := volume)
    have hm : (fun x => multiply κ.val.toBoundedContinuousFunction (B (f.toLp 2 volume)) x) =ᵐ[volume]
        fun x => κ x * B (f.toLp 2 volume) x := by
      filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
        (κ.val.toBoundedContinuousFunction.memLp_top.toLp κ.val.toBoundedContinuousFunction : Lp ℂ ⊤ volume)
        (B (f.toLp 2 volume)),
        (κ.val.toBoundedContinuousFunction.memLp_top (μ := volume)).coeFn_toLp] with x h₁ h₂
      exact h₁.trans (by simp only [ContinuousLinearMap.mul_apply', h₂]; rfl)
    filter_upwards [hm, hz, (ae_restrict_iff' (isClosed_tsupport _).measurableSet).mp hb,
      (ae_restrict_iff' (isClosed_tsupport _).measurableSet).mp hfc, ht]
      with x h₁ h₂ h₃ h₄ h₅
    change multiply κ.val.toBoundedContinuousFunction (B (f.toLp 2 volume)) x = _
    rw [h₁, h₅]
    change B (f.toLp 2 volume) x = _ at h₂
    rw [h₂]
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, h₃ hx]
      have hh := h₄ hx
      change (f.toLp 2 volume) (K.indicator e x) = f (K.indicator e x) at hh
      rw [hh, indicator_of_mem hx]
      rfl
    · have hk : κ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [chartTransport_apply, hk]
  rw [← heq]
  exact T.le_opNorm _

end GlobalElliptic

end
end

end OAI
