import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityShellRestriction

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_integral_preserving {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure A) (ν : Measure B)
    (F : A→B) (hF : MeasurePreserving F μ ν) (g : B→E) (hg : AEStronglyMeasurable g ν) :
    (∫ a,g (F a) ∂μ)=∫ b,g b ∂ν := by
  rw [←hF.map_eq] at hg ⊢
  exact (integral_map hF.measurable.aemeasurable hg).symm

lemma cavity_prod_front_swap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : A×B×C=>(p.2.1,p.1,p.2.2))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  exact (measurePreserving_prodAssoc ν μ ρ).comp
    ((Measure.measurePreserving_swap.prod (MeasurePreserving.id ρ)).comp
      (measurePreserving_prodAssoc μ ν ρ).symm)

lemma cavity_product_shuffle {A G B Y Z : Type*} [MeasurableSpace A] [MeasurableSpace G]
    [MeasurableSpace B] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure A) (γ : Measure G) (ν : Measure B) (η : Measure Y) (ζ : Measure Z)
    [SFinite μ] [SFinite γ] [SFinite ν] [SFinite η] [SFinite ζ] :
    MeasurePreserving (fun p : (A×G)×B×Y×Z=>(((p.1.1,p.2.2.1),(p.2.1,p.2.2.2)),p.1.2))
      ((μ.prod γ).prod (ν.prod (η.prod ζ))) (((μ.prod η).prod (ν.prod ζ)).prod γ) := by
  have h1:=(MeasurePreserving.id (μ.prod γ)).prod (cavity_prod_front_swap ν η ζ)
  have h2:=measurePreserving_prodAssoc μ γ (η.prod (ν.prod ζ))
  have h3:=(MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=γ) (ν:=η.prod (ν.prod ζ)))
  have h4:=(measurePreserving_prodAssoc μ (η.prod (ν.prod ζ)) γ).symm
  have h5:=((measurePreserving_prodAssoc μ η (ν.prod ζ)).symm).prod (MeasurePreserving.id γ)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

def cavityRowsAppend (N M d : ℕ) (a : Fin M→Fin N→ℝ) (b : Fin d→Fin N→ℝ) :
    Fin (M+d)→Fin N→ℝ := fun i=>Sum.elim a b (finSumFinEquiv.symm i)

lemma cavityRowsAppend_preserving (N M d : ℕ) :
    MeasurePreserving (fun p=>cavityRowsAppend N M d p.1 p.2)
      ((finitePatternRowsLaw N M).prod (finitePatternRowsLaw N d))
      (finitePatternRowsLaw N (M+d)) := by
  convert (measurePreserving_piCongrLeft (fun _ : Fin (M+d)=>Measure.pi fun _ : Fin N=>gaussianReal 0 1)
    finSumFinEquiv).comp (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin M⊕Fin d=>Measure.pi fun _ : Fin N=>gaussianReal 0 1)) using 1
  · funext p i
    simp only [Function.comp_apply,MeasurableEquiv.coe_piCongrLeft,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    rcases h : finSumFinEquiv.symm i with j | j <;> simp [cavityRowsAppend,Equiv.piCongrLeft_apply,h,Equiv.sumPiEquivProdPi]
  · rfl
  · rfl

lemma normalizedPatternEnergy_append (N M d : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin N→ℝ) (b : Fin d→Fin N→ℝ) (x : NormalizedSpin N) :
    normalizedPatternEnergy N (M+d) f (cavityRowsAppend N M d a b) x=
      normalizedPatternEnergy N M f a x+normalizedPatternEnergy N d f b x := by
  unfold normalizedPatternEnergy
  rw [←finSumFinEquiv.sum_comp]
  simp only [cavityRowsAppend,Equiv.symm_apply_apply,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma cavityShellPatternEnergy_append (n L M d : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (b : Fin d→Fin (n+1+L)→ℝ) (x : CavityShellSpin n L) :
    cavityShellPatternEnergy n L (M+d) f (cavityRowsAppend (n+1+L) M d a b) x=
      cavityShellPatternEnergy n L M f a x+cavityShellPatternEnergy n L d f b x := by
  exact normalizedPatternEnergy_append _ _ _ _ _ _ _


lemma cavity_gaussian_joint_log_integrable {A S I : Type*} [MeasurableSpace A]
    [MeasurableSpace S] [Fintype I] (Q : Measure A) [IsProbabilityMeasure Q]
    (μ : Measure S) [IsProbabilityMeasure μ] (H : A→S→ℝ) (V : S→EuclideanSpace ℝ I)
    (hH : Measurable (Function.uncurry H)) (hV : Measurable V)
    {C B : ℝ} (hC : 0≤C) (hB : 0≤B) (hHC : ∀ a x,|H a x|≤C) (hVB : ∀ x,‖V x‖≤B) :
    Integrable (fun p : A×EuclideanSpace ℝ I=>Real.log (tiltPartition μ
      (fun x=>H p.1 x+inner ℝ (V x) p.2) 1)) (Q.prod (stdGaussian (EuclideanSpace ℝ I))) := by
  have hi:=((integrable_const C).add
    ((IsGaussian.integrable_id (μ:=stdGaussian (EuclideanSpace ℝ I))).norm.const_mul B)).comp_snd Q
  have hm : Measurable (fun p : (A×EuclideanSpace ℝ I)×S=>H p.1.1 p.2+inner ℝ (V p.2) p.1.2) :=
    (hH.comp (measurable_fst.fst.prodMk measurable_snd)).add
      ((hV.comp measurable_snd).inner measurable_fst.snd)
  apply hi.mono' (by
    simpa only [tiltPartition,one_mul] using hm.exp.stronglyMeasurable.integral_prod_right'.measurable.log.aestronglyMeasurable)
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  apply tilt_log_partition_bound μ
    ((hH.comp (measurable_const.prodMk measurable_id)).add (hV.inner measurable_const))
    (add_nonneg hC (mul_nonneg hB (norm_nonneg _)))
  intro x
  exact (abs_add_le _ _).trans (add_le_add (hHC p.1 x)
    ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hVB x) (norm_nonneg _))))

def cavityShellLowLog (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (p : (Fin M→Fin (n+1+L)→ℝ)×BulkMark (n+1)) : ℝ :=
  Real.log (tiltPartition (cavityShellBaseLaw n L)
    (fun x=>cavityShellPatternEnergy n L M f p.1 x+inner ℝ (bulkFeature (n+1) v x.1) p.2) 1)

lemma cavityShellPatternEnergy_joint_measurable (n L M : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f p.1 p.2) := by
  change Measurable (fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>normalizedPatternEnergy (n+1+L) M f p.1 (cavityShellSpinEmbedding n L p.2))
  exact (normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp
    (f:=fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>(p.1,cavityShellSpinEmbedding n L p.2))
    (measurable_fst.prodMk ((cavityShellSpinEmbedding_measurable n L).comp measurable_snd))

lemma cavityShellLowLog_integrable (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (cavityShellLowLog n L M f v)
      ((finitePatternRowsLaw (n+1+L) M).prod (stdGaussian (BulkMark (n+1)))) := by
  let := cavityShellBaseLaw_probability n L hp
  apply cavity_gaussian_joint_log_integrable _ _ _ _
    (cavityShellPatternEnergy_joint_measurable n L M f)
    ((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst)
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
    (cavityShellPatternEnergy_bound n L M f)
  intro x
  exact (bulkFeature_norm _ _ _).le

lemma bulkExpectedLog_nested (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkExpectedLog n M f v=∫ a,∫ g,Real.log (tiltPartition (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 1) ∂stdGaussian (BulkMark (n+1))
      ∂finitePatternRowsLaw (n+1) M := by
  unfold bulkExpectedLog bulkDisorderLaw
  rw [integral_prod _ ((bulkLogPartition_memLp n M f v).integrable (by norm_num))]
  simp_rw [bulkLogPartition_eq]
  rfl

theorem cavity_expected_shell_restriction (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))-
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1))+
      (∫ p,cavityShellLowLog n L M f v p
        ∂(finitePatternRowsLaw (n+1+L) M).prod (stdGaussian (BulkMark (n+1))))≤
      bulkExpectedLog (n+L) M f v := by
  let := cavityShellBaseLaw_probability n L hp
  have hlo:=cavityShellLowLog_integrable n L M f v hp
  have hhi:=cavity_gaussian_joint_log_integrable (finitePatternRowsLaw (n+1+L) M)
    (cavityShellBaseLaw n L) (cavityShellPatternEnergy n L M f) (cavityShellFeature n L v)
    (cavityShellPatternEnergy_joint_measurable n L M f) (cavityShellFeature_measurable n L v)
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _) (cavityShellPatternEnergy_bound n L M f)
    (fun x=>(cavityShellFeature_norm n L v x).le)
  rw [integral_prod _ hlo,bulkExpectedLog_nested]
  rw [show n+L+1=n+1+L by omega]
  let : IsProbabilityMeasure (unitSphereLaw (n+1+L)) := by
    rw [show n+1+L=(n+L)+1 by omega]; infer_instance
  have hb:=cavity_gaussian_joint_log_integrable (finitePatternRowsLaw (n+1+L) M)
    (unitSphereLaw (n+1+L)) (normalizedPatternEnergy (n+1+L) M f) (bulkFeature (n+1+L) v)
    (normalizedPatternEnergy_continuous (n+1+L) M f).measurable (bulkFeature_continuous _ _).measurable
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _) (normalizedPatternEnergy_bound _ _ _)
    (fun x=>(bulkFeature_norm _ _ _).le)
  have hpoint : ∀ a,Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))-
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1))+
      (∫ g,cavityShellLowLog n L M f v (a,g) ∂stdGaussian (BulkMark (n+1)))≤
      ∫ g,Real.log (tiltPartition (unitSphereLaw (n+1+L))
        (bulkHamiltonian (n+1+L) M f v a g) 1) ∂stdGaussian (BulkMark (n+1+L)) := by
    intro a
    have hr:=cavity_gaussian_log_integrable (cavityShellBaseLaw n L)
      (cavityShellPatternEnergy_measurable n L M f a) (cavityShellFeature_measurable n L v)
      (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _) (cavityShellPatternEnergy_bound n L M f a)
      (fun x=>(cavityShellFeature_norm n L v x).le)
    have hb':=cavity_gaussian_log_integrable (unitSphereLaw (n+1+L))
      ((normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp (measurable_const.prodMk measurable_id))
      (bulkFeature_continuous (n+1+L) v).measurable (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
      (normalizedPatternEnergy_bound _ _ _ a) (fun x=>(bulkFeature_norm _ _ _).le)
    have hc:=cavity_true_shell_perturbation n L M f a v hC hv hp
    have hh:=integral_mono ((integrable_const _).add hr) hb'
      (cavity_actual_shell_log_restriction n L M f v a · hp)
    simp only [Pi.add_apply,Function.comp_def,id_eq] at hh
    rw [integral_add (integrable_const _) hr,integral_const,probReal_univ,one_smul] at hh
    dsimp [cavityShellLowLog] at ⊢
    change _≤∫ g,Real.log (tiltPartition (unitSphereLaw (n+1+L))
      (fun s=>normalizedPatternEnergy (n+1+L) M f a s+inner ℝ (bulkFeature (n+1+L) v s) g) 1) ∂_
    linarith [(abs_le.mp hc).1]
  have hi:=integral_mono ((integrable_const _).add hlo.integral_prod_left) hb.integral_prod_left hpoint
  simp only [Pi.add_apply] at hi
  change _≤∫ a,∫ g,Real.log (tiltPartition (unitSphereLaw (n+1+L))
    (fun s=>normalizedPatternEnergy (n+1+L) M f a s+inner ℝ (bulkFeature (n+1+L) v s) g) 1)
      ∂stdGaussian (BulkMark (n+1+L)) ∂finitePatternRowsLaw (n+1+L) M
  simpa only [integral_add (integrable_const _) hlo.integral_prod_left,integral_const,probReal_univ,one_smul,bulkHamiltonian] using hi
end SphericalPerceptronFreeEnergy

end

end OAI
