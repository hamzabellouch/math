import OAI.Analysis.IrrationalRotation.Model.PrefixPatternLaw
import OAI.Analysis.IrrationalRotation.Analysis.TriangularMarginals
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.PrefixPatterns

theorem measurable_replacement (I : Finset ℕ) : Measurable (replacement I) := by
  refine measurable_fst.prodMk (Measurable.of_eval fun i => ?_)
  by_cases hi : i ∈ I
  · simpa [replacement, selectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply i).comp (measurable_snd : Measurable (Prod.snd : EndpointPair → Base))
  · simpa [replacement, selectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : EndpointPair → Base))

theorem measurable_rectangleDensity {U V : Set Circle}
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    Measurable (rectangleDensity U V) :=
  measurable_const.indicator (hU.prod hV)

theorem lintegral_rectangleDensity {U V : Set Circle}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUpos : circleMeasure U ≠ 0) (hVpos : circleMeasure V ≠ 0) :
    ∫⁻ xz, rectangleDensity U V xz ∂(circleMeasure.prod circleMeasure) = 1 := by
  rw [rectangleDensity, lintegral_indicator_const (hU.prod hV), Measure.prod_prod]
  exact ENNReal.inv_mul_cancel (mul_ne_zero hUpos hVpos)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))

theorem ordered_cut_intervals {a b c d : ℝ} (hbc : b ≤ c)
    {x z : Circle} (hx : circleRepresentative x ∈ Set.Ico a b)
    (hz : circleRepresentative z ∈ Set.Ico c d) :
    circleRepresentative x < circleRepresentative z :=
  lt_of_lt_of_le hx.2 (hbc.trans hz.1)

theorem measurable_patternDensity (I : Finset ℕ) {g : Base → ℝ≥0∞}
    {U V : ℕ → Set Circle} (hg : Measurable g)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hV : ∀ i ∈ I, MeasurableSet (V i)) :
    Measurable (patternDensity I g U V) := by
  apply (hg.comp measurable_fst).mul
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_rectangleDensity (hU i hi) (hV i hi)).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

theorem patternDensity_replacement (I : Finset ℕ) (g : Base → ℝ≥0∞)
    (U V : ℕ → Set Circle) (xz : EndpointPair) :
    patternDensity I g U V (replacement I xz) = patternDensity I g U V xz := by
  unfold patternDensity replacement
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [selectedEndpoint, ite_eq_left hi]

theorem measurableSet_triangularEvent (I : Finset ℕ) :
    MeasurableSet (triangularEvent I) := by
  have hr : Measurable circleRepresentative :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  simp only [triangularEvent, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt (hr.comp ((measurable_pi_apply i).comp measurable_fst))
      (hr.comp ((measurable_pi_apply i).comp measurable_snd))

theorem patternDensity_zero_off_triangle (I : Finset ℕ) (g : Base → ℝ≥0∞)
    (U V : ℕ → Set Circle)
    (horder : ∀ i ∈ I, ∀ x ∈ U i, ∀ z ∈ V i,
      circleRepresentative x < circleRepresentative z)
    (xz : EndpointPair) (hxz : xz ∉ triangularEvent I) :
    patternDensity I g U V xz = 0 := by
  classical
  have hbad : ∃ i ∈ I, ¬ circleRepresentative (xz.1 i) < circleRepresentative (xz.2 i) := by
    simpa only [triangularEvent, Set.mem_ofPred_eq, not_forall, exists_prop] using hxz
  obtain ⟨i, hi, hnot⟩ := hbad
  have hout : (xz.1 i, xz.2 i) ∉ U i ×ˢ V i := by
    intro h
    exact hnot (horder i hi _ h.1 _ h.2)
  have hz : rectangleDensity (U i) (V i) (xz.1 i, xz.2 i) = 0 :=
    Set.indicator_of_notMem hout _
  unfold patternDensity
  rw [Finset.prod_eq_zero hi hz, mul_zero]

theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} {r : Y → ℝ≥0∞}
    (hf : Measurable f) (hr : Measurable r) :
    (μ.withDensity (r ∘ f)).map f = (μ.map f).withDensity r := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hr hf]
  rfl

theorem patternLaw_eq_withDensity (I : Finset ℕ) {g : Base → ℝ≥0∞}
    {U V : ℕ → Set Circle} (hg : Measurable g)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hV : ∀ i ∈ I, MeasurableSet (V i))
    (horder : ∀ i ∈ I, ∀ x ∈ U i, ∀ z ∈ V i,
      circleRepresentative x < circleRepresentative z) :
    patternLaw I g U V = (triangularLaw I).withDensity (patternDensity I g U V) := by
  have hind : (triangularEvent I).indicator (patternDensity I g U V) =
      patternDensity I g U V := by
    funext xz
    by_cases hxz : xz ∈ triangularEvent I
    · exact Set.indicator_of_mem hxz _
    · rw [Set.indicator_of_notMem hxz,
        patternDensity_zero_off_triangle I g U V horder xz hxz]
  have hrestrict : (baseMeasure.prod baseMeasure).withDensity (patternDensity I g U V) =
      ((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).withDensity
        (patternDensity I g U V) := by
    rw [← withDensity_indicator (measurableSet_triangularEvent I), hind]
  have hcomp : patternDensity I g U V = patternDensity I g U V ∘ replacement I := by
    funext xz
    exact (patternDensity_replacement I g U V xz).symm
  rw [patternLaw, hrestrict, hcomp,
    map_withDensity_comp _ (measurable_replacement I)
      (measurable_patternDensity I hg hU hV)]
  rw [← hcomp]
  rfl

theorem patternLaw_absolutelyContinuous_of_order (I : Finset ℕ) (g : Base → ℝ≥0∞)
    (U V : ℕ → Set Circle)
    (horder : ∀ i ∈ I, ∀ x ∈ U i, ∀ z ∈ V i,
      circleRepresentative x < circleRepresentative z) :
    patternLaw I g U V ≪ triangularLaw I := by
  have hind : (triangularEvent I).indicator (patternDensity I g U V) =
      patternDensity I g U V := by
    funext xz
    by_cases hxz : xz ∈ triangularEvent I
    · exact Set.indicator_of_mem hxz _
    · rw [Set.indicator_of_notMem hxz,
        patternDensity_zero_off_triangle I g U V horder xz hxz]
  unfold patternLaw triangularLaw
  rw [← hind, withDensity_indicator (measurableSet_triangularEvent I)]
  exact (withDensity_absolutelyContinuous _ _).map (measurable_replacement I)

theorem patternLaw_absolutelyContinuous (I : Finset ℕ) {g : Base → ℝ≥0∞}
    {U V : ℕ → Set Circle} (hg : Measurable g)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hV : ∀ i ∈ I, MeasurableSet (V i))
    (horder : ∀ i ∈ I, ∀ x ∈ U i, ∀ z ∈ V i,
      circleRepresentative x < circleRepresentative z) :
    patternLaw I g U V ≪ triangularLaw I := by
  rw [patternLaw_eq_withDensity I hg hU hV horder]
  exact withDensity_absolutelyContinuous _ _

theorem map_withDensity_comp_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} {r : Y → ℝ≥0∞}
    (hf : Measurable f) (hr : AEMeasurable r (μ.map f)) :
    (μ.withDensity (r ∘ f)).map f = (μ.map f).withDensity r := by
  have heq : r ∘ f =ᵐ[μ] hr.mk r ∘ f :=
    ae_of_ae_map hf.aemeasurable hr.ae_eq_mk
  calc
    (μ.withDensity (r ∘ f)).map f = (μ.withDensity (hr.mk r ∘ f)).map f := by
      rw [withDensity_congr_ae heq]
    _ = (μ.map f).withDensity (hr.mk r) :=
      map_withDensity_comp μ hf hr.measurable_mk
    _ = (μ.map f).withDensity r := (withDensity_congr_ae hr.ae_eq_mk).symm

theorem aemeasurable_patternDensity (I : Finset ℕ) {g : Base → ℝ≥0∞}
    {U V : ℕ → Set Circle} (hg : AEMeasurable g baseMeasure)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hV : ∀ i ∈ I, MeasurableSet (V i)) :
    AEMeasurable (patternDensity I g U V) (triangularLaw I) := by
  have hfst : QuasiMeasurePreserving Prod.fst (triangularLaw I) baseMeasure := by
    refine ⟨measurable_fst, ?_⟩
    rw [triangularLaw_first_marginal]
    exact withDensity_absolutelyContinuous _ _
  apply (hg.comp_quasiMeasurePreserving hfst).mul
  apply Measurable.aemeasurable
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_rectangleDensity (hU i hi) (hV i hi)).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

theorem patternLaw_eq_withDensity_ae (I : Finset ℕ) {g : Base → ℝ≥0∞}
    {U V : ℕ → Set Circle} (hg : AEMeasurable g baseMeasure)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hV : ∀ i ∈ I, MeasurableSet (V i))
    (horder : ∀ i ∈ I, ∀ x ∈ U i, ∀ z ∈ V i,
      circleRepresentative x < circleRepresentative z) :
    patternLaw I g U V = (triangularLaw I).withDensity (patternDensity I g U V) := by
  have hind : (triangularEvent I).indicator (patternDensity I g U V) =
      patternDensity I g U V := by
    funext xz
    by_cases hxz : xz ∈ triangularEvent I
    · exact Set.indicator_of_mem hxz _
    · rw [Set.indicator_of_notMem hxz,
        patternDensity_zero_off_triangle I g U V horder xz hxz]
  have hrestrict : (baseMeasure.prod baseMeasure).withDensity (patternDensity I g U V) =
      ((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).withDensity
        (patternDensity I g U V) := by
    rw [← withDensity_indicator (measurableSet_triangularEvent I), hind]
  have hcomp : patternDensity I g U V = patternDensity I g U V ∘ replacement I := by
    funext xz
    exact (patternDensity_replacement I g U V xz).symm
  have hm : AEMeasurable (patternDensity I g U V)
      (((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).map (replacement I)) :=
    aemeasurable_patternDensity I hg hU hV
  rw [patternLaw, hrestrict, hcomp,
    map_withDensity_comp_ae _ (measurable_replacement I) hm, ← hcomp]
  rfl

theorem triangularLaw_absolutelyContinuous_prefix_sum {D I : Finset ℕ}
    (hID : I ⊆ D) :
    triangularLaw I ≪ ∑ J ∈ D.powerset, triangularLaw J := by
  apply Measure.absolutelyContinuous_of_le
  exact Finset.single_le_sum (fun J _ => bot_le) (Finset.mem_powerset.mpr hID)

theorem mixtureLaw_absolutelyContinuous_prefix_sum
    {C : Type*} [Fintype C] (D : Finset ℕ) (w : C → ℝ≥0∞)
    (I : C → Finset ℕ) (g : C → Base → ℝ≥0∞)
    (U V : C → ℕ → Set Circle)
    (hI : ∀ c, I c ⊆ D) (hg : ∀ c, Measurable (g c))
    (hU : ∀ c i, i ∈ I c → MeasurableSet (U c i))
    (hV : ∀ c i, i ∈ I c → MeasurableSet (V c i))
    (horder : ∀ c i, i ∈ I c → ∀ x ∈ U c i, ∀ z ∈ V c i,
      circleRepresentative x < circleRepresentative z) :
    mixtureLaw w I g U V ≪ ∑ J ∈ D.powerset, triangularLaw J := by
  classical
  have hc : ∀ c, w c • patternLaw (I c) (g c) (U c) (V c) ≪
      ∑ J ∈ D.powerset, triangularLaw J := by
    intro c
    exact ((patternLaw_absolutelyContinuous (I c) (hg c) (hU c) (hV c) (horder c)).trans
      (triangularLaw_absolutelyContinuous_prefix_sum (hI c))).smul_left (w c)
  have hs : ∀ s : Finset C,
      (∑ c ∈ s, w c • patternLaw (I c) (g c) (U c) (V c)) ≪
        ∑ J ∈ D.powerset, triangularLaw J := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Measure.AbsolutelyContinuous.zero _
    | @insert c s hcs ih =>
      rw [Finset.sum_insert hcs]
      exact (hc c).add_left ih
  exact hs Finset.univ

theorem ae_mixtureLaw_of_ae_triangularLaw
    {C : Type*} [Fintype C] (D : Finset ℕ) (w : C → ℝ≥0∞)
    (I : C → Finset ℕ) (g : C → Base → ℝ≥0∞)
    (U V : C → ℕ → Set Circle)
    (hI : ∀ c, I c ⊆ D) (hg : ∀ c, Measurable (g c))
    (hU : ∀ c i, i ∈ I c → MeasurableSet (U c i))
    (hV : ∀ c i, i ∈ I c → MeasurableSet (V c i))
    (horder : ∀ c i, i ∈ I c → ∀ x ∈ U c i, ∀ z ∈ V c i,
      circleRepresentative x < circleRepresentative z)
    {P : EndpointPair → Prop} (hP : ∀ J ⊆ D, ∀ᵐ xy ∂triangularLaw J, P xy) :
    ∀ᵐ xy ∂mixtureLaw w I g U V, P xy := by
  apply (mixtureLaw_absolutelyContinuous_prefix_sum D w I g U V hI hg hU hV horder).ae_le
  change ∀ᵐ xy ∂(∑ J ∈ D.powerset, triangularLaw J), P xy
  rw [ae_iff]
  have hzero : ∀ J ∈ D.powerset, triangularLaw J {xy | ¬ P xy} = 0 := by
    intro J hJ
    exact ae_iff.mp (hP J (Finset.mem_powerset.mp hJ))
  have hsum : (∑ J ∈ D.powerset, triangularLaw J) {xy | ¬ P xy} =
      ∑ J ∈ D.powerset, triangularLaw J {xy | ¬ P xy} := by
    exact Measure.finsetSum_apply _ _ _
  rw [hsum]
  exact Finset.sum_eq_zero hzero

end Invariant233.ProductModel.PrefixPatterns

end

end OAI
