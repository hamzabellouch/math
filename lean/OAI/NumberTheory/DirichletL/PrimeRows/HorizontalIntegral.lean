import OAI.NumberTheory.DirichletL.PrimeRows.BufferedJoinDecay

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedRow_horizontal_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (tx υ r : ℝ) (hr : 0<r) :
    Measurable (fun p : ℝ × (ℝ × ℝ)=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
      p.1 υ r ((tx,p.2.1),p.2.2)) := by
  have hR : Continuous (fun t : ℝ=>mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)).continuous
  have hcoords : Continuous (fun p : ℝ × (ℝ × ℝ)=>(((p.1:ℂ)+tx*I,(υ:ℂ)+p.2.2*I),(r:ℂ)+p.2.1*I)) := by fun_prop
  have hscale := (sourceScale_continuous X Y Z hX hY hZ).comp hcoords
  have hprof : Measurable (fun p : ℝ × (ℝ × ℝ)=>profile W0 W1
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    unfold profile
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hR.measurable.comp (by fun_prop)
    · exact hW.measurable.comp (by fun_prop)
  have hsource : Measurable (fun p : ℝ × (ℝ × ℝ)=>sourceMellinWeight W0 W1 X Y Z
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    simp_rw [sourceMellinWeight_eq_scale]
    exact hscale.measurable.mul hprof
  have hphysical := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun p : ℝ × (ℝ × ℝ)=>(p.1:ℂ)+tx*I) (fun p : ℝ × (ℝ × ℝ)=>(υ:ℂ)+p.2.2*I)
    (fun p : ℝ × (ℝ × ℝ)=>(r:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold continuedRowOnLines continuedPhysicalRowKernel
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul hsource
      apply Finset.measurable_prod
      intro i hi
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _
          (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero).ne'
      · fun_prop
    · unfold frequencyWeight
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
      · fun_prop
  · exact hphysical.const_mul _

lemma horizontal_integral_bound (F : ℝ→(ℝ×ℝ)→ℂ) (l r C : ℝ) (hlr : l≤r) (_hC : 0≤C)
    (hm : Measurable (Function.uncurry F))
    (hi : ∀v∈Ioc l r,Integrable (F v) (volume.prod volume))
    (hb : ∀v∈Ioc l r,(∫q : ℝ×ℝ,‖F v q‖ ∂volume.prod volume)≤C) :
    Integrable (fun q : ℝ×ℝ=>∫v : ℝ in l..r,F v q) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖∫v : ℝ in l..r,F v q‖ ∂volume.prod volume)≤(r-l)*C := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let ν : Measure (ℝ×ℝ) := volume.prod volume
  have hm' : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := hm.aestronglyMeasurable
  have hnorm : Integrable (fun v=>∫q,‖F v q‖ ∂ν) μ := by
    apply (integrable_const C).mono' hm'.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    exact hb v hv
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff hm').mpr
    refine ⟨?_,hnorm⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hi v hv
  have hj : Integrable (fun q=>∫v,F v q ∂μ) ν := hprod.integral_prod_right
  simp only [intervalIntegral.integral_of_le hlr]
  refine ⟨hj,?_⟩
  calc
    _ ≤ ∫q,∫v,‖F v q‖ ∂μ ∂ν := integral_mono hj.norm hprod.integral_norm_prod_right
      (fun q=>norm_integral_le_integral_norm _)
    _ = ∫v,∫q,‖F v q‖ ∂ν ∂μ := integral_integral_swap hprod.norm.swap
    _ ≤ ∫v,C ∂μ := integral_mono_ae hnorm (integrable_const C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hb v hv)
    _ = _ := by
      dsimp [μ]
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hlr,smul_eq_mul]

end SevenEighths.ProbeHighRowFamily

end

end OAI
