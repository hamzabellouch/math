import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace Problem367

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSingletonClass A] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condExp_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap S inferInstance] =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => ∫ ω, f ω ∂μ[|S ⁻¹' {a}] := by
  let s := S ⁻¹' {a}
  have hs : MeasurableSet s := hS (measurableSet_singleton a)
  have hs' : MeasurableSet[MeasurableSpace.comap S inferInstance] s :=
    ⟨{a}, measurableSet_singleton a, rfl⟩
  by_cases hμs : μ s = 0
  · rw [show S ⁻¹' {a} = s from rfl, Measure.restrict_eq_zero.2 hμs]
    rfl
  have havg : (∫ ω, (∫ x, f x ∂μ[|s]) ∂μ.restrict s) =
      ∫ ω, f ω ∂μ.restrict s := by
    rw [integral_const, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨hμs, measure_ne_top _ _⟩), one_mul]
  refine (condExp_restrict_ae_eq_restrict hS.comap_le hs' hf).symm.trans ?_
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hS.comap_le hf.restrict
  · intro t _ _
    exact (integrable_const _).integrableOn
  · rintro t ⟨u, hu, rfl⟩ _
    rw [Measure.restrict_restrict (hS hu)]
    by_cases ha : a ∈ u
    · have heq : S ⁻¹' u ∩ s = s := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨And.right, fun h => ⟨h ▸ ha, h⟩⟩
      rw [heq]
      exact havg
    · have heq : S ⁻¹' u ∩ s = ∅ := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro h hEq
        exact ha (hEq ▸ h)
      simp [heq]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem condExp_indicator_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {t : Set Ω} (ht : MeasurableSet t) :
    μ⟦t | MeasurableSpace.comap S inferInstance⟧ =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => μ[|S ⁻¹' {a}].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_comap_eq_cond_on_fiber hS a ((integrable_const (1 : ℝ)).indicator ht)

theorem indepFun_cond_fiber_of_condIndepFun [StandardBorelSpace Ω]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hXY : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ)
    (a : A) : IndepFun X Y μ[|S ⁻¹' {a}] := by
  by_cases hμa : μ (S ⁻¹' {a}) = 0
  · rw [cond_eq_zero_of_meas_eq_zero hμa]
    simp [indepFun_iff_measure_inter_preimage_eq_mul]
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hcond := (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mp hXY s t hs ht
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a ((hX hs).inter (hY ht))
  have hfirst := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hX hs)
  have hsecond := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hY ht)
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (X ⁻¹' s ∩ Y ⁻¹' t) =
        μ[|S ⁻¹' {a}].real (X ⁻¹' s) * μ[|S ⁻¹' {a}].real (Y ⁻¹' t) := by
    filter_upwards [hcond', hleft, hfirst, hsecond] with ω h h₁ h₂ h₃
    simpa only [h₁, h₂, h₃] using h
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_mul] using hω

theorem iIndepFun_cond_fiber_of_iCondIndepFun [StandardBorelSpace Ω]
    {ι : Type*} {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {S : Ω → A} {X : ∀ i, Ω → B i}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hXI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X μ)
    (a : A) (hμa : μ (S ⁻¹' {a}) ≠ 0) : iIndepFun X μ[|S ⁻¹' {a}] := by
  classical
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hsets
  have hcond := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB X hX).mp hXI I hsets
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hmeas : MeasurableSet (⋂ i ∈ I, X i ⁻¹' sets i) :=
    Finset.measurableSet_biInter I (fun i hi => hX i (hsets i hi))
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a hmeas
  have heach : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), ∀ i ∈ I,
      (μ⟦X i ⁻¹' sets i | MeasurableSpace.comap S inferInstance⟧) ω =
        μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    apply (Finset.eventually_all I).mpr
    intro i hi
    exact condExp_indicator_comap_eq_cond_on_fiber hS a (hX i (hsets i hi))
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (⋂ i ∈ I, X i ⁻¹' sets i) =
        ∏ i ∈ I, μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    filter_upwards [hcond', hleft, heach] with ω h h₁ h₂
    rw [h₁] at h
    simp only [Finset.prod_apply] at h
    exact h.trans (Finset.prod_congr rfl h₂)
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top (fun i hi => measure_ne_top _ _))).mp
  simpa only [measureReal_def, ENNReal.toReal_prod] using hω

theorem condExp_comap_discrete [Countable A] {S : Ω → A} (hS : Measurable S)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap S inferInstance] =ᵐ[μ]
      fun ω => ∫ x, f x ∂μ[|S ⁻¹' {S ω}] := by
  have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} →
      (μ[f | MeasurableSpace.comap S inferInstance]) ω =
        ∫ x, f x ∂μ[|S ⁻¹' {a}] := by
    apply ae_all_iff.mpr
    intro a
    exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp
      (condExp_comap_eq_cond_on_fiber hS a hf)
  filter_upwards [hAll] with ω hω
  exact hω (S ω) rfl

theorem condIndepFun_iff_indepFun_cond_fibers [StandardBorelSpace Ω] [Countable A]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y) :
    CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ ↔
      ∀ a : A, μ (S ⁻¹' {a}) ≠ 0 → IndepFun X Y μ[|S ⁻¹' {a}] := by
  constructor
  · intro h a _
    exact indepFun_cond_fiber_of_condIndepFun hS hX hY h a
  · intro h
    apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mpr
    intro s t hs ht
    have hOn (a : A) : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
        (μ⟦X ⁻¹' s ∩ Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω =
          (μ⟦X ⁻¹' s | MeasurableSpace.comap S inferInstance⟧) ω *
            (μ⟦Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω := by
      by_cases hμa : μ (S ⁻¹' {a}) = 0
      · rw [Measure.restrict_eq_zero.mpr hμa]
        simp
      have hprod := (h a hμa).measure_inter_preimage_eq_mul s t hs ht
      have hreal := congrArg ENNReal.toReal hprod
      simp only [ENNReal.toReal_mul] at hreal
      filter_upwards
        [condExp_indicator_comap_eq_cond_on_fiber hS a ((hX hs).inter (hY ht)),
         condExp_indicator_comap_eq_cond_on_fiber hS a (hX hs),
         condExp_indicator_comap_eq_cond_on_fiber hS a (hY ht)] with ω h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      exact hreal
    have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} →
        (μ⟦X ⁻¹' s ∩ Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω =
          (μ⟦X ⁻¹' s | MeasurableSpace.comap S inferInstance⟧) ω *
            (μ⟦Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω := by
      apply ae_all_iff.mpr
      intro a
      exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp (hOn a)
    filter_upwards [hAll] with ω hω
    exact hω (S ω) rfl

omit [IsFiniteMeasure μ] in

theorem ae_of_ae_restrict_fibers [Countable A] {S : Ω → A} (hS : Measurable S)
    {p : Ω → Prop} (h : ∀ a : A, ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} → p ω := by
    apply ae_all_iff.mpr
    intro a
    exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp (h a)
  filter_upwards [hAll] with ω hω
  exact hω (S ω) rfl

theorem iCondIndepFun_iff_iIndepFun_cond_fibers [StandardBorelSpace Ω] [Countable A]
    {ι : Type*} {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {S : Ω → A} {X : ∀ i, Ω → B i}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i)) :
    iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X μ ↔
      ∀ a : A, μ (S ⁻¹' {a}) ≠ 0 → iIndepFun X μ[|S ⁻¹' {a}] := by
  classical
  constructor
  · intro h a hμa
    exact iIndepFun_cond_fiber_of_iCondIndepFun hS hX h a hμa
  · intro h
    apply (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB X hX).mpr
    intro I sets hsets
    apply ae_of_ae_restrict_fibers hS
    intro a
    by_cases hμa : μ (S ⁻¹' {a}) = 0
    · rw [Measure.restrict_eq_zero.mpr hμa]
      simp
    have hprod := (h a hμa).measure_inter_preimage_eq_mul I hsets
    have hreal := congrArg ENNReal.toReal hprod
    simp only [ENNReal.toReal_prod] at hreal
    have hmeas : MeasurableSet (⋂ i ∈ I, X i ⁻¹' sets i) :=
      Finset.measurableSet_biInter I (fun i hi => hX i (hsets i hi))
    have heach : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), ∀ i ∈ I,
        (μ⟦X i ⁻¹' sets i | MeasurableSpace.comap S inferInstance⟧) ω =
          μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
      apply (Finset.eventually_all I).mpr
      intro i hi
      exact condExp_indicator_comap_eq_cond_on_fiber hS a (hX i (hsets i hi))
    filter_upwards [condExp_indicator_comap_eq_cond_on_fiber hS a hmeas, heach]
      with ω h₁ h₂
    simp only [Finset.prod_apply]
    rw [h₁, Finset.prod_congr rfl h₂]
    exact hreal

end Problem367

end

end OAI
