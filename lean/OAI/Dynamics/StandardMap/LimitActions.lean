import OAI.Dynamics.StandardMap.ArrayActions

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTestExtend_translate (g : C_c(NonAffineArray,ℝ)) (r : DyadicTime) (d : DistanceArray) :
    arrayTestExtend (g.comp (nonaffineTranslation r).toCocompactMap) d=
      arrayTestExtend g (arrayTranslate r d) := by
  by_cases hd : d∈affineLocus
  · rw [arrayTestExtend_affine _ d hd,arrayTestExtend_affine _ _ ((arrayTranslate_mem_affine_iff r d).mpr hd)]
  · exact (arrayTestExtend_apply _ ⟨d,hd⟩).trans (arrayTestExtend_apply g (nonaffineTranslation r ⟨d,hd⟩)).symm
lemma arrayTestExtend_dilate (g : C_c(NonAffineArray,ℝ)) (d : DistanceArray) :
    arrayTestExtend (g.comp nonaffineDilation) d=arrayTestExtend g (arrayDilate d) := by
  by_cases hd : d∈affineLocus
  · rw [arrayTestExtend_affine _ d hd,arrayTestExtend_affine _ _ ((arrayDilate_mem_affine_iff d).mpr hd)]
  · exact (arrayTestExtend_apply _ ⟨d,hd⟩).trans (arrayTestExtend_apply g (nonaffineDilate ⟨d,hd⟩)).symm
lemma integral_translate_nonaffine (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (r : DyadicTime) (hμ : μ.map (arrayTranslate r)=μ) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart μ)=
      ∫ d,g d ∂nonaffinePart μ := by
  rw [← integral_arrayTestExtend,← integral_arrayTestExtend]
  simp_rw [arrayTestExtend_translate]
  rw [← integral_map (f := fun d => arrayTestExtend g d) (continuous_arrayTranslate r).measurable.aemeasurable (arrayTestExtend g).continuous.aestronglyMeasurable,hμ]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
instance : L.multi.Regular := L.multi_regular
instance : L.terminal.Regular := L.terminal_regular
lemma multiLaw_translate_eventually (r : DyadicTime) :
    ∀ᶠ i in atTop, (S.multiLaw i).map (arrayTranslate r)=S.multiLaw i := by
  obtain ⟨p,hp⟩ := dyadic_aligned_eventually r
  filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p] with i hi
  obtain ⟨a,ha⟩ := hp _ hi
  exact scaleLaw_translate _ _ _ _ _ r a ha
lemma terminalLaw_translate_eventually (r : DyadicTime) :
    ∀ᶠ i in atTop, (S.terminalLaw i).map (arrayTranslate r)=S.terminalLaw i := by
  obtain ⟨p,hp⟩ := dyadic_aligned_eventually r
  filter_upwards [S.exponent_tendsto.eventually_ge_atTop p] with i hi
  obtain ⟨a,ha⟩ := hp _ hi
  exact scaleLaw_translate _ _ _ _ _ r a ha
lemma multi_integral_translate (r : DyadicTime) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineTranslation r d) ∂L.multi)=∫ d,g d ∂L.multi := by
  have hh : (fun i => ∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart (S.multiLaw i))
      =ᶠ[L.filter] (fun i => ∫ d,g d ∂nonaffinePart (S.multiLaw i)) := by
    filter_upwards [L.refines (S.multiLaw_translate_eventually r)] with i hi
    exact integral_translate_nonaffine (S.multiLaw i) r hi g
  exact tendsto_nhds_unique (L.multi_converges (g.comp (nonaffineTranslation r).toCocompactMap))
    ((L.multi_converges g).congr' hh.symm)
lemma terminal_integral_translate (r : DyadicTime) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineTranslation r d) ∂L.terminal)=∫ d,g d ∂L.terminal := by
  have hh : (fun i => ∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart (S.terminalLaw i))
      =ᶠ[L.filter] (fun i => ∫ d,g d ∂nonaffinePart (S.terminalLaw i)) := by
    filter_upwards [L.refines (S.terminalLaw_translate_eventually r)] with i hi
    exact integral_translate_nonaffine (S.terminalLaw i) r hi g
  exact tendsto_nhds_unique (L.terminal_converges (g.comp (nonaffineTranslation r).toCocompactMap))
    ((L.terminal_converges g).congr' hh.symm)
lemma multi_translate (r : DyadicTime) : L.multi.map (nonaffineTranslation r)=L.multi := by
  let := Measure.Regular.map (μ := L.multi) (nonaffineTranslation r)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) (nonaffineTranslation r).continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  exact S.multi_integral_translate L r g
lemma terminal_translate (r : DyadicTime) : L.terminal.map (nonaffineTranslation r)=L.terminal := by
  let := Measure.Regular.map (μ := L.terminal) (nonaffineTranslation r)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) (nonaffineTranslation r).continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  exact S.terminal_integral_translate L r g
end CriticalScaleSequence
end StandardMapEntropy

end OAI
