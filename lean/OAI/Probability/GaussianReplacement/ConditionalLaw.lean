import OAI.Probability.GaussianReplacement.FreshRows

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) (f : A×B → D) : Kernel A D :=
  (Kernel.id ×ₖ κ).map f

lemma dependentMapKernel_markov {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) [IsMarkovKernel κ] (f : A×B → D)
    (hf : Measurable f) : IsMarkovKernel (dependentMapKernel κ f) :=
  Kernel.IsMarkovKernel.map _ hf

lemma dependentMapKernel_apply {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) [IsSFiniteKernel κ] (f : A×B → D)
    (hf : Measurable f) (a : A) : dependentMapKernel κ f a = (κ a).map (fun b => f (a,b)) := by
  rw [dependentMapKernel,Kernel.map_apply _ hf,Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map hf (measurable_prodMk_left (x:=a))]
  rfl

lemma compProd_dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (μ : Measure A) [SFinite μ]
    (κ : Kernel A B) [IsSFiniteKernel κ] (f : A×B → D) (hf : Measurable f) :
    μ ⊗ₘ dependentMapKernel κ f = (μ ⊗ₘ κ).map (fun z => (z.1,f z)) := by
  have : IsSFiniteKernel (dependentMapKernel κ f) := by unfold dependentMapKernel; infer_instance
  ext t ht
  rw [Measure.compProd_apply ht,Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.compProd_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply lintegral_congr
  intro a
  rw [dependentMapKernel_apply κ f hf a,
    Measure.map_apply (show Measurable (fun b => f (a,b)) from hf.comp measurable_prodMk_left)
      (ht.preimage (measurable_prodMk_left (x:=a)))]
  rfl

lemma compProd_conditional_prod_swap {C S X : Type*} [MeasurableSpace C]
    [MeasurableSpace S] [MeasurableSpace X] (μ : Measure C) [SFinite μ]
    (κ : Kernel C S) [IsSFiniteKernel κ] (γ : Measure X) [SFinite γ] :
    ((μ.prod γ) ⊗ₘ κ.comap Prod.fst measurable_fst).map
      (fun z : (C×X)×S => ((z.1.1,z.2),z.1.2)) = (μ ⊗ₘ κ).prod γ := by
  have h1 := compProd_prod_assoc μ (Kernel.const C γ) κ
  rw [Measure.compProd_const] at h1
  rw [←h1,Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.symm.measurable]
  have h2 := compProd_prod_assoc μ κ (Kernel.const C γ)
  have hconst : (Kernel.const C γ).comap (Prod.fst : C×S → C) measurable_fst = Kernel.const _ γ := rfl
  rw [hconst,Measure.compProd_const] at h2
  rw [←h2,←Kernel.map_prod_swap (Kernel.const C γ) κ,Measure.compProd_map measurable_swap,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap measurable_swap)]
  rfl

def scalarProjectionKernel {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) : Kernel (C×Vector d) ℝ :=
  dependentMapKernel (κ.comap Prod.fst measurable_fst)
    (fun z : (C×Vector d)×Sphere d => ⟪(z.2:Vector d),z.1.2⟫)

instance scalarProjectionKernel_markov {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsMarkovKernel κ] : IsMarkovKernel (scalarProjectionKernel κ) :=
  dependentMapKernel_markov _ _ (by fun_prop)

lemma scalarProjectionKernel_apply {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsSFiniteKernel κ] (z : C×Vector d) :
    scalarProjectionKernel κ z = (κ z.1).map (fun s : Sphere d => ⟪(s:Vector d),z.2⟫) :=
  dependentMapKernel_apply _ _ (by fun_prop) _

def scalarObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×Vector d) : (C×Vector d)×ℝ :=
  ((z.1.1,z.2),⟪(z.1.2:Vector d),z.2⟫)

lemma measurable_scalarObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (scalarObservation (d:=d) (C:=C)) := by unfold scalarObservation; fun_prop

def scalarObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) : Measure ((C×Vector d)×ℝ) :=
  (Γ.prod (stdGaussian (Vector d))).map scalarObservation

instance scalarObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : IsProbabilityMeasure (scalarObservationLaw Γ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_scalarObservation.aemeasurable).mpr inferInstance

lemma scalarObservationLaw_disintegrate {d : ℕ} [Nonempty (Sphere d)]
    {C : Type*} [MeasurableSpace C] (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ scalarProjectionKernel Γ.condKernel = scalarObservationLaw Γ := by
  rw [scalarProjectionKernel,compProd_dependentMapKernel _ _ _ (by fun_prop),scalarObservationLaw]
  have he := compProd_conditional_prod_swap Γ.fst Γ.condKernel (stdGaussian (Vector d))
  rw [Γ.disintegrate Γ.condKernel] at he
  rw [←he,Measure.map_map measurable_scalarObservation (by fun_prop)]
  rfl

lemma scalarObservationLaw_fst {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    (scalarObservationLaw Γ).fst = Γ.fst.prod (stdGaussian (Vector d)) := by
  rw [←scalarObservationLaw_disintegrate Γ,Measure.fst_compProd]

lemma scalarCube_projection {d : ℕ} {C : Type*} [MeasurableSpace C]
    (κ : Kernel C (Sphere d)) [IsSFiniteKernel κ] (z : C×Vector d) (s : Sphere d) (δ : ℝ) :
    scalarCube (scalarProjectionKernel κ z) ⟪(s:Vector d),z.2⟫ δ =
      ∫⁻ t : Sphere d, cubeKernel δ ⟪(t:Vector d)-(s:Vector d),z.2⟫ ∂κ z.1 := by
  rw [scalarCube,scalarProjectionKernel_apply,lintegral_map
    (f:=fun t : ℝ => cubeKernel δ (t-⟪(s:Vector d),z.2⟫))
    ((measurable_cubeKernel δ).comp (by fun_prop)) (by fun_prop)]
  simp only [inner_sub_left]

lemma scalarObservationLaw_kernel_ac {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ a ∂Γ.fst.prod (stdGaussian (Vector d)), scalarProjectionKernel Γ.condKernel a ≪ volume := by
  have hac := (klDiv_ne_top_iff.mp h).1
  have hgv : gaussianReal 0 1 ≪ (volume : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
    exact withDensity_absolutelyContinuous _ _
  change scalarObservationLaw Γ ≪ (scalarObservationLaw Γ).fst.prod (gaussianReal 0 1) at hac
  have hh : (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ scalarProjectionKernel Γ.condKernel ≪
      (Γ.fst.prod (stdGaussian (Vector d))) ⊗ₘ Kernel.const _ (gaussianReal 0 1) := by
    rw [Measure.compProd_const,scalarObservationLaw_disintegrate Γ,←scalarObservationLaw_fst Γ]
    exact hac
  exact hh.kernel_of_compProd.mono (fun a ha => ha.trans hgv)

lemma scalarObservationLaw_density {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ((scalarObservationLaw Γ).fst.prod volume).withDensity
      (fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2) = scalarObservationLaw Γ := by
  rw [scalarObservationLaw_fst,←scalarObservationLaw_disintegrate Γ]
  exact kernel_scalarDensity_withDensity _ _ (scalarObservationLaw_kernel_ac Γ h)

lemma scalarObservationLaw_ae_limit {d : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (h : conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ z ∂scalarObservationLaw Γ, Tendsto
      (fun n : ℕ => scalarCube (scalarProjectionKernel Γ.condKernel z.1) z.2 (1/(n:ℝ)))
      atTop (𝓝 (scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2)) := by
  have ha : scalarObservationLaw Γ ≪ (scalarObservationLaw Γ).fst.prod volume := by
    have hh := withDensity_absolutelyContinuous
      ((scalarObservationLaw Γ).fst.prod volume)
      (fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2)
    rwa [scalarObservationLaw_density Γ h] at hh
  exact ha.ae_le (kernel_scalarDensity_ae_limit (scalarObservationLaw Γ).fst
    (scalarProjectionKernel Γ.condKernel))

lemma prod_map_swap23 {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (μ : Measure A) (ν : Measure B) (π : Measure D)
    [SFinite μ] [SFinite ν] [SFinite π] :
    ((μ.prod ν).prod π).map (fun z : (A×B)×D => ((z.1.1,z.2),z.1.2)) = (μ.prod π).prod ν := by
  have h : ((μ.prod ν).prod π).map (fun z : (A×B)×D => ((z.1.1,z.2),z.1.2)) =
      (((μ.prod ν).prod π).map MeasurableEquiv.prodAssoc).map
        ((MeasurableEquiv.prodAssoc : (A×D)×B ≃ᵐ A×(D×B)).symm ∘ Prod.map id Prod.swap) := by
    rw [Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
    rfl
  rw [h,Measure.prodAssoc_prod,←Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap),←Measure.map_prod_map _ _ measurable_id measurable_swap,
    Measure.map_id,Measure.prod_swap,←Measure.prodAssoc_prod,MeasurableEquiv.map_symm_map]



def residualLabelObservation {d r : ℕ} {C : Type*}
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ :=
  (((w.1.1.1,(w.2,label w.2 (w.1.1.2:Vector d))),w.1.2),⟪(w.1.1.2:Vector d),w.1.2⟫)

lemma measurable_residualLabelObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (residualLabelObservation (d:=d) (r:=r) (C:=C)) := by
  unfold residualLabelObservation label
  fun_prop

def residualLabelLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    Measure (((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ) :=
  (P.prod (gaussianRows r d)).map residualLabelObservation

instance residualLabelLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (residualLabelLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_residualLabelObservation.aemeasurable).mpr inferInstance

lemma residualLabelLaw_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    residualLabelLaw (Γ.prod (stdGaussian (Vector d))) r =
      scalarObservationLaw (residualLaw Γ r) := by
  unfold scalarObservationLaw residualLaw
  have he : ((Γ.prod (gaussianRows r d)).map residualObservation).prod (stdGaussian (Vector d)) =
      ((Γ.prod (gaussianRows r d)).prod (stdGaussian (Vector d))).map
        (Prod.map residualObservation id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map
      (Γ.prod (gaussianRows r d)) (stdGaussian (Vector d)) measurable_residualObservation measurable_id
  rw [he,←prod_map_swap23 Γ (stdGaussian (Vector d)) (gaussianRows r d),
    Measure.map_map (measurable_residualObservation.prodMap measurable_id) (by fun_prop),
    Measure.map_map measurable_scalarObservation
      ((measurable_residualObservation.prodMap measurable_id).comp (by fun_prop))]
  rfl

lemma klDiv_prod_same {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure B) [IsProbabilityMeasure π] : klDiv (μ.prod π) (ν.prod π) = klDiv μ ν := by
  rw [←Measure.compProd_const,←Measure.compProd_const]
  exact klDiv_compProd_left _ _ _

lemma residualLabelLaw_kl_le {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    klDiv (residualLabelLaw P r) (scalarObservationLaw (residualLaw P.fst r)) ≤
      klDiv P (P.fst.prod (stdGaussian (Vector d))) := by
  rw [←residualLabelLaw_fresh P.fst r]
  exact (klDiv_map_le _ _ measurable_residualLabelObservation).trans_eq
    (klDiv_prod_same _ _ _)

def residualExact {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (w : ((C×Sphere d)×Vector d)×Rows r d) : ℝ≥0∞ :=
  scalarDensity (scalarProjectionKernel (residualLaw Γ r).condKernel
    (residualLabelObservation w).1) (residualLabelObservation w).2 /
    residualScale Γ w.1.1 w.2

lemma measurable_residualExact {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    Measurable (residualExact (r:=r) Γ) := by
  exact ((measurable_scalarDensity (scalarProjectionKernel (residualLaw Γ r).condKernel)).comp
    measurable_residualLabelObservation).div ((measurable_residualScale Γ).comp
      (measurable_fst.fst.prodMk measurable_snd))

lemma residualExact_finite {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ]
    (w : ((C×Sphere d)×Vector d)×Rows r d) : residualExact Γ w ≠ ∞ := by
  exact ENNReal.div_ne_top (scalarDensity_finite _ _)
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower Γ w.1.1 w.2)))

lemma residualCube_ae_limit_actual {d r : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (href : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞) :
    ∀ᵐ w ∂P.prod (gaussianRows r d), Tendsto
      (fun n : ℕ => residualCube P.fst (1/(n:ℝ)) w) atTop (𝓝 (residualExact P.fst w)) := by
  have hk := ne_top_of_le_ne_top hKL (residualLabelLaw_kl_le P r)
  have ha := (klDiv_ne_top_iff.mp hk).1
  have ht := ha.ae_le (scalarObservationLaw_ae_limit (residualLaw P.fst r) href)
  have hh := ae_of_ae_map measurable_residualLabelObservation.aemeasurable ht
  filter_upwards [hh] with w hw
  have hd := ENNReal.Tendsto.div_const hw (Or.inr
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (residualScale_lower P.fst w.1.1 w.2))))
  convert hd using 1
  · funext n
    dsimp only [residualLabelObservation,Prod.fst,Prod.snd]
    rw [scalarCube_projection]
    rfl
  · rfl

lemma residualCube_log_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfin : ∀ᵐ z ∂residualLaw P.fst r, reciprocalScale ((residualLaw P.fst r).condKernel z.1) z.2 ≠ ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ w, ENNReal.ofReal (Real.log (1+(residualCube P.fst δ w).toReal)) ∂P.prod (gaussianRows r d) ≤
      ENNReal.ofReal ((klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q +
        Real.log (1+5*kernelSmallBallConstant)) := by
  have hc : 0 ≤ 5*kernelSmallBallConstant := by
    have := kernelSmallBallConstant_ge_two
    linarith
  simpa only [integral_const,probReal_univ,one_smul] using mixed_entropy_log_bound_ae P
    (stdGaussian (Vector d)) (gaussianRows r d) hKL (residualCube P.fst δ)
    (measurable_residualCube P.fst δ) (residualCube_finite P.fst δ) (residualCube_integral_finite P.fst δ)
    (fun _ => 5*kernelSmallBallConstant) measurable_const (fun _=>hc) (integrable_const _) hq
    (residualCube_moment P.fst hr hd hqr hmargin hfin hδ)

lemma residualExact_log_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfin : ∀ᵐ z ∂residualLaw P.fst r, reciprocalScale ((residualLaw P.fst r).condKernel z.1) z.2 ≠ ∞)
    (href : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞) :
    Integrable (fun w => Real.log (1+(residualExact P.fst w).toReal)) (P.prod (gaussianRows r d)) ∧
    (∫ w, Real.log (1+(residualExact P.fst w).toReal) ∂P.prod (gaussianRows r d)) ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q +
        Real.log (1+5*kernelSmallBallConstant) := by
  have hR : 0 ≤ (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q +
      Real.log (1+5*kernelSmallBallConstant) := by
    apply add_nonneg (by positivity)
    apply Real.log_nonneg
    have := kernelSmallBallConstant_ge_two
    linarith
  apply (log_bound_consequences _ _ (measurable_residualExact P.fst) _ hR ?_).1
  apply log_lintegral_bound_of_ae_tendsto _ (fun n => residualCube P.fst (1/(n:ℝ)))
    (residualExact P.fst) (fun n => measurable_residualCube P.fst _) (residualExact_finite P.fst)
    (residualCube_ae_limit_actual P hKL href)
  intro n hn
  exact residualCube_log_bound P hKL hr hd hq hqr hmargin hfin (by positivity)




lemma klDiv_map_bound_of_llr_le {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (R : Measure D) [IsProbabilityMeasure R]
    (f : A → D) (hf : Measurable f) (ha : P.map f ≪ R)
    (u : A → ℝ) (hu : Integrable u P)
    (hb : ∀ᵐ w ∂P, llr (P.map f) R (f w) ≤ u w) :
    klDiv (P.map f) R ≠ ∞ ∧ (klDiv (P.map f) R).toReal ≤ ∫ w, u w ∂P := by
  let : IsProbabilityMeasure (P.map f) := inferInstance
  have hri : Integrable (fun x => (R.rnDeriv (P.map f) x).toReal) (P.map f) := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ:=R) (ν:=P.map f) (s:=Set.univ) (measure_ne_top _ _))
  have hri' : Integrable (fun w => (R.rnDeriv (P.map f) (f w)).toReal) P :=
    (integrable_map_measure (Measurable.ennreal_toReal (Measure.measurable_rnDeriv _ _)).aestronglyMeasurable
      hf.aemeasurable).mp hri
  have hlo : ∀ᵐ w ∂P, -(R.rnDeriv (P.map f) (f w)).toReal ≤ llr (P.map f) R (f w) := by
    filter_upwards [ae_of_ae_map hf.aemeasurable (exp_neg_llr ha)] with w hw
    have ht := Real.add_one_le_exp (-llr (P.map f) R (f w))
    rw [hw] at ht
    linarith
  have hi : Integrable (fun w => llr (P.map f) R (f w)) P := integrable_of_le_of_le
    ((measurable_llr _ _).comp hf).aestronglyMeasurable hlo hb hri'.neg hu
  have hi' : Integrable (llr (P.map f) R) (P.map f) :=
    (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable hf.aemeasurable).mpr hi
  refine ⟨klDiv_ne_top ha hi',?_⟩
  rw [toReal_klDiv_of_measure_eq ha (by simp),integral_map hf.aemeasurable
    (measurable_llr _ _).aestronglyMeasurable]
  exact integral_mono_ae hi hu hb

lemma klDiv_map_cross_bound {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (Q R : Measure D)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (f : A → D) (hf : Measurable f) (hPQ : klDiv (P.map f) Q ≠ ∞) (hQR : Q ≪ R)
    (u : A → ℝ) (hu : Integrable u P)
    (hb : ∀ᵐ w ∂P, llr Q R (f w) ≤ u w) :
    klDiv (P.map f) R ≠ ∞ ∧ (klDiv (P.map f) R).toReal ≤
      (klDiv (P.map f) Q).toReal + ∫ w, u w ∂P := by
  let : IsProbabilityMeasure (P.map f) := inferInstance
  obtain ⟨ha,hi⟩ := klDiv_ne_top_iff.mp hPQ
  have hi' : Integrable (fun w => llr (P.map f) Q (f w)) P :=
    (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable hf.aemeasurable).mp hi
  have he := ae_of_ae_map hf.aemeasurable (llr_chain_ae (P.map f) Q R ha hQR)
  have hb' : ∀ᵐ w ∂P, llr (P.map f) R (f w) ≤ llr (P.map f) Q (f w)+u w := by
    filter_upwards [he,hb] with w hw hb
    rw [hw]
    linarith
  obtain ⟨hfin,hbound⟩ := klDiv_map_bound_of_llr_le P R f hf (ha.trans hQR) _ (hi'.add hu) hb'
  refine ⟨hfin,?_⟩
  simp only [Pi.add_apply] at hbound
  rw [integral_add hi' hu,←integral_map hf.aemeasurable (measurable_llr _ _).aestronglyMeasurable,
    ←toReal_klDiv_of_measure_eq ha (by simp)] at hbound
  exact hbound



lemma residualSignalLaw {d r : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    (P.prod (gaussianRows r d)).map
      (fun w => residualObservation (w.1.1,w.2)) = residualLaw P.fst r := by
  unfold residualLaw
  have he : (P.fst.prod (gaussianRows r d)) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) := by
    simpa only [Measure.map_id,Measure.fst] using Measure.map_prod_map P (gaussianRows r d) measurable_fst measurable_id
  rw [he,Measure.map_map measurable_residualObservation (measurable_fst.prodMap measurable_id)]
  rfl

lemma density_positive_ae {A : Type*} [MeasurableSpace A]
    (Q Λ : Measure A) [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (he : Λ.withDensity p = Q) :
    ∀ᵐ a ∂Q, 0 < p a := by
  have ha : Q ≪ Λ := by rw [←he]; exact withDensity_absolutelyContinuous _ _
  have hr : Q.rnDeriv Λ =ᵐ[Λ] p := by rw [←he]; exact Measure.rnDeriv_withDensity _ hp
  filter_upwards [ha.ae_le hr,Measure.rnDeriv_pos ha] with a h1 h2
  rwa [←h1]

lemma log_le_log_scale_add {p A : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ∞)
    (hA : 0 < A) (hAt : A ≠ ∞) :
    Real.log p.toReal ≤ Real.log A.toReal+Real.log (1+(p/A).toReal) := by
  have hp' := ENNReal.toReal_pos hp.ne' hpt
  have hA' := ENNReal.toReal_pos hA.ne' hAt
  rw [ENNReal.toReal_div]
  have hl := Real.log_le_log (div_pos hp' hA') (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num) : p.toReal/A.toReal ≤ 1+p.toReal/A.toReal)
  rw [Real.log_div hp'.ne' hA'.ne'] at hl
  linarith

def hybridRowConstant : ℝ := cauchyTiltConstant+Real.log (1+5*kernelSmallBallConstant)

lemma residual_reference_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfresh : conditionalReferenceKL (scalarObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞)
    (hnext : conditionalReferenceKL (cauchyObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1) ≠ ∞)
    (hlabel : (residualLabelLaw P r).snd = gaussianReal 0 1) :
    klDiv (residualLabelLaw P r)
      ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1)) ≠ ∞ ∧
    (klDiv (residualLabelLaw P r)
      ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1))).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal +
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q + hybridRowConstant +
      (conditionalReferenceKL (cauchyObservationLaw (residualLaw P.fst r)) (gaussianReal 0 1)).toReal := by
  let Γ := residualLaw P.fst r
  let M := P.prod (gaussianRows r d)
  let Q := scalarObservationLaw Γ
  let R := Q.fst.prod (gaussianReal 0 1)
  let Λ := Q.fst.prod (volume : Measure ℝ)
  let p : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ → ℝ≥0∞ :=
    fun z => scalarDensity (scalarProjectionKernel Γ.condKernel z.1) z.2
  have hp : Measurable p := measurable_scalarDensity _
  have hpQ : Λ.withDensity p = Q := scalarObservationLaw_density Γ hfresh
  have hgR : Λ.withDensity (fun z => ENNReal.ofReal (gaussianPDFReal 0 1 z.2)) = R := by
    rw [show (fun z : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ =>
      ENNReal.ofReal (gaussianPDFReal 0 1 z.2)) = (fun z => gaussianPDF 0 1 z.2) from rfl,
      ←prod_withDensity_right (measurable_gaussianPDF 0 1)]
    change Q.fst.prod _ = Q.fst.prod (gaussianReal 0 1)
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
  have hdens := llr_of_two_densities Q R Λ p hp hpQ
    (fun z => gaussianPDFReal 0 1 z.2) (by fun_prop)
    (fun z => gaussianPDFReal_pos _ _ _ (by norm_num)) hgR
  have hobsKL := ne_top_of_le_ne_top hKL (residualLabelLaw_kl_le P r)
  have hobsAC := (klDiv_ne_top_iff.mp hobsKL).1
  have hpos := ae_of_ae_map measurable_residualLabelObservation.aemeasurable
    (hobsAC.ae_le (density_positive_ae Q Λ p hp hpQ))
  have hllr := ae_of_ae_map measurable_residualLabelObservation.aemeasurable (hobsAC.ae_le hdens.2)
  obtain ⟨hAfinite,hAi,hAb⟩ := reciprocalScale_experiment_bound Γ Γ.condKernel hnext
  have hmap : M.map (fun w => residualObservation (w.1.1,w.2)) = Γ := residualSignalLaw P
  have hmapm : Measurable (fun w : ((C×Sphere d)×Vector d)×Rows r d => residualObservation (w.1.1,w.2)) :=
    measurable_residualObservation.comp (measurable_fst.fst.prodMk measurable_snd)
  have hAm : Measurable (fun z : (C×(Rows r d×(Fin r→ℝ)))×Sphere d =>
      Real.log (reciprocalScale (Γ.condKernel z.1) z.2).toReal) :=
    (reciprocalScale_kernel_measurable Γ.condKernel).ennreal_toReal.log
  have hAi' : Integrable (fun w => Real.log (residualScale P.fst w.1.1 w.2).toReal) M := by
    exact (integrable_map_measure hAm.aestronglyMeasurable hmapm.aemeasurable).mp (hmap.symm ▸ hAi)
  have hAb' : (∫ w, Real.log (residualScale P.fst w.1.1 w.2).toReal ∂M) ≤
      cauchyTiltConstant-standardGaussianEntropy+
        (conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1)).toReal := by
    have he := integral_map (μ:=M) hmapm.aemeasurable hAm.aestronglyMeasurable
    rw [hmap] at he
    exact he ▸ hAb
  have hAf : ∀ᵐ w ∂M, residualScale P.fst w.1.1 w.2 ≠ ∞ := by
    have ht : ∀ᵐ z ∂M.map (fun w => residualObservation (w.1.1,w.2)),
        reciprocalScale (Γ.condKernel z.1) z.2 ≠ ∞ := by rwa [hmap]
    exact ae_of_ae_map hmapm.aemeasurable ht
  obtain ⟨hNi,hNb⟩ := residualExact_log_bound P hKL hr hd hq hqr hmargin hAfinite hfresh
  obtain ⟨hgi,hgb⟩ := standardGaussian_cross_entropy (residualLabelLaw P r) hlabel
  have hgm : Measurable (fun z : ((C×(Rows r d×(Fin r→ℝ)))×Vector d)×ℝ =>
      Real.log (gaussianPDFReal 0 1 z.2)) := by fun_prop
  have hgi' : Integrable (fun w => Real.log (gaussianPDFReal 0 1 (residualLabelObservation w).2)) M :=
    (integrable_map_measure hgm.aestronglyMeasurable measurable_residualLabelObservation.aemeasurable).mp hgi
  let u : ((C×Sphere d)×Vector d)×Rows r d → ℝ := fun w =>
    Real.log (residualScale P.fst w.1.1 w.2).toReal + Real.log (1+(residualExact P.fst w).toReal) -
      Real.log (gaussianPDFReal 0 1 (residualLabelObservation w).2)
  have hui : Integrable u M := (hAi'.add hNi).sub hgi'
  have hu : ∀ᵐ w ∂M, llr Q R (residualLabelObservation w) ≤ u w := by
    filter_upwards [hllr,hpos,hAf] with w hl hp0 hAt
    rw [hl]
    have ht := log_le_log_scale_add hp0 (scalarDensity_finite _ _)
      (lt_of_lt_of_le (by norm_num) (residualScale_lower P.fst w.1.1 w.2)) hAt
    exact sub_le_sub_right ht _
  obtain ⟨hfin,hbound⟩ := klDiv_map_cross_bound M Q R residualLabelObservation
    measurable_residualLabelObservation hobsKL hdens.1 u hui hu
  refine ⟨hfin,?_⟩
  have hK : (klDiv (residualLabelLaw P r) Q).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal :=
    ENNReal.toReal_mono hKL (residualLabelLaw_kl_le P r)
  have hgb' : -(∫ w, Real.log (gaussianPDFReal 0 1 (residualLabelObservation w).2) ∂M) = standardGaussianEntropy := by
    rw [←integral_map measurable_residualLabelObservation.aemeasurable hgm.aestronglyMeasurable]
    simpa only [integral_neg,residualLabelLaw,M] using hgb
  dsimp only [u] at hbound
  have hsum : Integrable (fun w => Real.log (residualScale P.fst w.1.1 w.2).toReal +
      Real.log (1+(residualExact P.fst w).toReal)) M := hAi'.add hNi
  rw [integral_sub hsum hgi',integral_add hAi' hNi] at hbound
  change _ ≤ _ + _ + (cauchyTiltConstant+Real.log (1+5*kernelSmallBallConstant)) + _
  dsimp only [M,Q,R,Γ,residualLabelLaw] at hbound hK hAb' hNb hgb' ⊢
  linarith



end CurrentProjection

end

end OAI
