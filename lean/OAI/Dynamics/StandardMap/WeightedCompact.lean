import OAI.Dynamics.StandardMap.WeightTruncation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def realWeight {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))
lemma integral_realWeight {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→ℝ)
    (hf:Measurable f) (h0:∀x,0≤f x) (g:X→ℝ) :
    (∫x,g x ∂realWeight μ f)=∫x,g x*f x ∂μ := by
  rw [realWeight,integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (h0 _),smul_eq_mul,mul_comm]
lemma realWeight_finite {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→ℝ) (hf:Integrable f μ) :
    IsFiniteMeasure (realWeight μ f) := isFiniteMeasure_withDensity_ofReal hf.2
structure CompactWeightLimit {ι:Type*} (l:Filter ι) (μ:ι→Measure DistanceArray) (f:DistanceArray→ℝ) where
  law : Measure DistanceArray
  regular : law.Regular
  finite : IsFiniteMeasure law
  converges : ∀g:C(DistanceArray,ℝ), Tendsto (fun i => ∫d,g d*f d ∂μ i) l (𝓝 (∫d,g d ∂law))
lemma exists_compact_weight_limit {ι:Type*} (l:Ultrafilter ι) (μ:ι→Measure DistanceArray)
    [∀i,IsFiniteMeasure (μ i)] (f:DistanceArray→ℝ) (hf:Continuous f) (h0:∀d,0≤f d)
    (C:ℝ) (hb:∀ᶠi in (l:Filter ι),(∫d,f d ∂μ i)≤C) :
    Nonempty (CompactWeightLimit (l:Filter ι) μ f) := by
  let ν:=fun i => realWeight (μ i) f
  have (i:ι) : IsFiniteMeasure (ν i) := realWeight_finite _ _ (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hbound (g:C_c(DistanceArray,ℝ)) : ∃D:ℝ,∀ᶠi in (l:Filter ι),|∫d,g d ∂ν i|≤D := by
    obtain ⟨D,hD⟩:=isCompact_univ.exists_bound_of_continuousOn g.continuous.continuousOn
    refine ⟨max D 0*C,?_⟩
    filter_upwards [hb] with i hi
    rw [integral_realWeight _ _ hf.measurable h0]
    have hdom:∀ d, |g d*f d| ≤ max D 0*f d := by
      intro d; rw [abs_mul,abs_of_nonneg (h0 d)]
      exact mul_le_mul_of_nonneg_right ((hD d (mem_univ d)).trans (le_max_left _ _)) (h0 d)
    have hInt:=integral_mono ((g.continuous.mul hf).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_const.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hdom (μ:=μ i)
    have hAbs:|∫d,g d*f d ∂μ i|≤∫d,|g d*f d| ∂μ i := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ:=μ i) (fun d => g d*f d)
    simp only [Pi.mul_apply] at hInt
    rw [integral_const_mul] at hInt
    exact hAbs.trans (hInt.trans (mul_le_mul_of_nonneg_left hi (le_max_right _ _)))
  obtain ⟨νlim,hlimr,hliml,hlim⟩:=exists_vague_limit l ν hbound
  have:=hliml
  refine ⟨⟨νlim,hlimr,inferInstance,?_⟩⟩
  intro g
  let gc:C_c(DistanceArray,ℝ):=⟨g,HasCompactSupport.of_compactSpace _⟩
  have hh:=hlim gc
  dsimp only [ν] at hh
  simp_rw [integral_realWeight _ _ hf.measurable h0] at hh
  exact hh
lemma open_measure_le_of_integral_bound {X:Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (μ:Measure X) [μ.Regular] {U:Set X} (hU:IsOpen U) (C:ℝ)
    (hb:∀g:C_c(X,ℝ),(∀x,0≤g x) → (∀x,g x≤1) → (∀x∉U,g x=0) → ∫x,g x ∂μ≤C) :
    μ U≤ENNReal.ofReal C := by
  rw [hU.measure_eq_iSup_isCompact μ]
  simp only [iSup_le_iff]
  intro K hKU hK
  obtain ⟨⟨f,hfc⟩,hfK,hfU,hfs,hfr⟩:=exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  let g:C_c(X,ℝ):=⟨⟨f,hfc⟩,hfs⟩
  have hh:=hb g (fun x => (hfr x).1) (fun x => (hfr x).2) (fun x hx => hfU hx)
  have hμ:μ K≤ENNReal.ofReal (∫x,g x ∂μ) := (hfc.integrable_of_hasCompactSupport hfs).measure_le_integral (Eventually.of_forall (fun x => (hfr x).1)) (fun x hx => (hfK hx).ge)
  exact hμ.trans (ENNReal.ofReal_le_ofReal hh)
end StandardMapEntropy

end OAI
