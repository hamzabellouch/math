import Mathlib

namespace OAI

/-! Localized Pullback. -/

section

 

noncomputable section
open Set MeasureTheory Topology Filter
open scoped ENNReal ContDiff

namespace GlobalElliptic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_restrict_le_of_jacobian_lower (f : E → E) (hf : Measurable f)
    (f' : E → E →L[ℝ] E) {K : Set E} (hK : MeasurableSet K)
    (hder : ∀ x ∈ K, HasFDerivWithinAt f (f' x) K x) (hinj : InjOn f K)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ x ∈ K, δ ≤ |(f' x).det|) :
    Measure.map f (volume.restrict K) ≤ ENNReal.ofReal δ⁻¹ • (volume : Measure E) := by
  have hineq : (volume.restrict K).withDensity (fun _ : E => (1 : ℝ≥0∞)) ≤
      (volume.restrict K).withDensity
        (fun x => ENNReal.ofReal δ⁻¹ * ENNReal.ofReal |(f' x).det|) := by
    apply withDensity_mono
    filter_upwards [self_mem_ae_restrict hK] with x hx
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (show (1:ℝ) ≤ δ⁻¹ * |(f' x).det| by
      rw [← div_eq_inv_mul, le_div_iff₀ hδ]
      simpa using hlower x hx)
  rw [withDensity_const, one_smul] at hineq
  change volume.restrict K ≤ (volume.restrict K).withDensity
    (ENNReal.ofReal δ⁻¹ • (fun x => ENNReal.ofReal |(f' x).det|)) at hineq
  rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top] at hineq
  have hmap := Measure.map_mono hineq hf
  rw [Measure.map_smul _ hf.aemeasurable,
    map_withDensity_abs_det_fderiv_eq_addHaar volume hK.nullMeasurableSet hder hinj] at hmap
  apply hmap.trans
  gcongr
  exact Measure.restrict_le_self

 

theorem exists_map_restrict_bound (f : E → E) (f' : E → E →L[ℝ] E)
    {K : Set E} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hder : ∀ x ∈ K, HasFDerivWithinAt f (f' x) K x) (hinj : InjOn f K)
    (hcont : ContinuousOn (fun x => |(f' x).det|) K)
    (hnonzero : ∀ x ∈ K, (f' x).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      Measurable (K.indicator f) ∧
      Measure.map (K.indicator f) (volume.restrict K) ≤ ENNReal.ofReal C • (volume : Measure E) := by
  classical
  have hmeas : Measurable (K.indicator f) := by
    exact hf.measurable_piecewise continuous_zero.continuousOn hK.isClosed.measurableSet
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn hne hcont
    let δ := |(f' x).det|
    have hδ : 0 < δ := abs_pos.mpr (hnonzero x hx)
    refine ⟨δ⁻¹, (inv_pos.mpr hδ).le, hmeas, ?_⟩
    apply map_restrict_le_of_jacobian_lower _ hmeas f' hK.isClosed.measurableSet
      (fun y hy => (hder y hy).congr (fun z hz => indicator_of_mem hz f)
        (indicator_of_mem hy f))
      (hinj.congr (fun y hy => (indicator_of_mem hy f).symm)) hδ
    intro y hy
    exact hxmin hy
  · have he : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst K
    exact ⟨0, le_rfl, hmeas, by simp⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chart_fderiv_det_ne_zero (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) : (fderiv ℝ e x).det ≠ 0 := by
  have h₁ := ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have h₂ := ((hs.contDiffAt (e.open_target.mem_nhds (e.mapsTo hx))).differentiableAt (by simp)).hasFDerivAt
  have hcomp := h₂.comp x h₁
  have hi : (fun y => e.symm (e y)) =ᶠ[nhds x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy using e.left_inv hy
  have heq : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ E :=
    (hcomp.congr_of_eventuallyEq hi.symm).unique (hasFDerivAt_id x)
  have hdet := congrArg ContinuousLinearMap.det heq
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap) =
    LinearMap.det (LinearMap.id) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hz
  change (fderiv ℝ e.symm (e x)).det * (fderiv ℝ e x).det = 1 at hdet
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

 

theorem chart_map_restrict_bound (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ Measurable (K.indicator e) ∧
      Measure.map (K.indicator e) (volume.restrict K) ≤ ENNReal.ofReal C • (volume : Measure E) := by
  apply exists_map_restrict_bound e (fderiv ℝ e) hK (e.continuousOn.mono hKe)
    (fun x hx => (((he.contDiffAt (e.open_source.mem_nhds (hKe hx))).differentiableAt
      (by simp)).hasFDerivAt).hasFDerivWithinAt) (e.injOn.mono hKe)
  · exact (ContinuousLinearMap.continuous_det.comp_continuousOn
      (he.continuousOn_fderiv_of_isOpen e.open_source (by simp))).abs.mono hKe
  · exact fun x hx => chart_fderiv_det_ne_zero e he hs (hKe hx)

end GlobalElliptic

namespace MeasureTheory.Lp
open scoped _root_.MeasureTheory _root_.MeasureTheory.Lp
variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : _root_.MeasureTheory.Measure α} {ν : _root_.MeasureTheory.Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]

def extendZeroFun {K : Set α} (hK : MeasurableSet K) (u : _root_.MeasureTheory.Lp F p (μ.restrict K)) :
    _root_.MeasureTheory.Lp F p μ :=
  ((_root_.MeasureTheory.memLp_indicator_iff_restrict hK).mpr (_root_.MeasureTheory.Lp.memLp u)).toLp (K.indicator u)

omit [NormedSpace ℝ F] [Fact (1 ≤ p)] in
lemma coeFn_extendZeroFun {K : Set α} (hK : MeasurableSet K) (u : _root_.MeasureTheory.Lp F p (μ.restrict K)) :
    extendZeroFun hK u =ᵐ[μ] K.indicator u := _root_.MeasureTheory.MemLp.coeFn_toLp _

omit [NormedSpace ℝ F] [Fact (1 ≤ p)] in
lemma extendZeroFun_add {K : Set α} (hK : MeasurableSet K) (u v : _root_.MeasureTheory.Lp F p (μ.restrict K)) :
    extendZeroFun hK (u + v) = extendZeroFun hK u + extendZeroFun hK v := by
  apply _root_.MeasureTheory.Lp.ext
  filter_upwards [coeFn_extendZeroFun hK (u + v), coeFn_extendZeroFun hK u,
    coeFn_extendZeroFun hK v, _root_.MeasureTheory.Lp.coeFn_add (extendZeroFun hK u) (extendZeroFun hK v),
    (_root_.MeasureTheory.ae_restrict_iff' hK).mp (_root_.MeasureTheory.Lp.coeFn_add u v)] with x h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₄, Pi.add_apply, h₂, h₃]
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx, h₅ hx, Pi.add_apply]
  · simp only [indicator_of_notMem hx, add_zero]

omit [Fact (1 ≤ p)] in
lemma extendZeroFun_smul {K : Set α} (hK : MeasurableSet K) (c : ℝ)
    (u : _root_.MeasureTheory.Lp F p (μ.restrict K)) : extendZeroFun hK (c • u) = c • extendZeroFun hK u := by
  apply _root_.MeasureTheory.Lp.ext
  filter_upwards [coeFn_extendZeroFun hK (c • u), coeFn_extendZeroFun hK u,
    _root_.MeasureTheory.Lp.coeFn_smul c (extendZeroFun hK u),
    (_root_.MeasureTheory.ae_restrict_iff' hK).mp (_root_.MeasureTheory.Lp.coeFn_smul c u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, Pi.smul_apply, h₂]
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx, h₄ hx, Pi.smul_apply]
  · simp only [indicator_of_notMem hx, smul_zero]

omit [NormedSpace ℝ F] [Fact (1 ≤ p)] in
lemma norm_extendZeroFun {K : Set α} (hK : MeasurableSet K) (u : _root_.MeasureTheory.Lp F p (μ.restrict K)) :
    ‖extendZeroFun hK u‖ = ‖u‖ := by
  rw [extendZeroFun, _root_.MeasureTheory.Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hK, _root_.MeasureTheory.Lp.norm_def]

 
def extendZero {K : Set α} (hK : MeasurableSet K) :
    _root_.MeasureTheory.Lp F p (μ.restrict K) →ₗᵢ[ℝ] _root_.MeasureTheory.Lp F p μ where
  toFun := extendZeroFun hK
  map_add' := extendZeroFun_add hK
  map_smul' := extendZeroFun_smul hK
  norm_map' := norm_extendZeroFun hK

lemma coeFn_extendZero {K : Set α} (hK : MeasurableSet K) (u : _root_.MeasureTheory.Lp F p (μ.restrict K)) :
    extendZero hK u =ᵐ[μ] K.indicator u := coeFn_extendZeroFun hK u

 
def pullbackBounded (f : α → β) (hf : Measurable f) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (h : _root_.MeasureTheory.Measure.map f μ ≤ C • ν) : _root_.MeasureTheory.Lp F p ν →L[ℝ] _root_.MeasureTheory.Lp F p μ :=
  (_root_.MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ f ⟨hf, rfl⟩).toContinuousLinearMap ∘L
    _root_.MeasureTheory.Lp.LpToLpOfMeasureLeSMul hC h

lemma coeFn_pullbackBounded (f : α → β) (hf : Measurable f) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (h : _root_.MeasureTheory.Measure.map f μ ≤ C • ν) (u : _root_.MeasureTheory.Lp F p ν) :
    pullbackBounded f hf hC h u =ᵐ[μ] (fun x => u (f x)) := by
  change _root_.MeasureTheory.Lp.compMeasurePreserving f ⟨hf, rfl⟩ (_root_.MeasureTheory.Lp.LpToLpOfMeasureLeSMul hC h u) =ᵐ[μ] _
  apply (_root_.MeasureTheory.Lp.coeFn_compMeasurePreserving _ ⟨hf, rfl⟩).trans
  exact _root_.MeasureTheory.ae_of_ae_map hf.aemeasurable (_root_.MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul hC h u)

lemma pullbackBounded_norm_le (f : α → β) (hf : Measurable f) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (h : _root_.MeasureTheory.Measure.map f μ ≤ C • ν) (u : _root_.MeasureTheory.Lp F p ν) :
    ‖pullbackBounded f hf hC h u‖ ≤ C.toReal ^ (1 / p).toReal * ‖u‖ := by
  change ‖_root_.MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ f ⟨hf, rfl⟩ (_root_.MeasureTheory.Lp.LpToLpOfMeasureLeSMul hC h u)‖ ≤ _
  rw [LinearIsometry.norm_map]
  have hb : ‖(_root_.MeasureTheory.Lp.LpToLpOfMeasureLeSMul hC h : _root_.MeasureTheory.Lp F p ν →L[ℝ] _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.Measure.map f μ))‖ ≤
      C.toReal ^ (1 / p).toReal := _root_.MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul_le hC h
  apply ((_root_.MeasureTheory.Lp.LpToLpOfMeasureLeSMul hC h).le_opNorm u).trans
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg u)

end MeasureTheory.Lp

end
end

end OAI
