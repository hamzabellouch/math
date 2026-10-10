import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkConcentration
import OAI.Probability.Perceptron.Cavity.CavityBlockProduct
import OAI.Probability.Perceptron.Cavity.CavityShellPerturbation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma unitSphere_cavityAmbient_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map Subtype.val=
      ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L)).map
        (fun p=>cavityNormalizedVec (n+1) L p.1 p.2) := by
  have h:=congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>μ.map (gaussianBlockJoin (n+1) L))
    (sphereBlock_scaled_product_law n L)
  have hm : Measurable (fun u : NormalizedSpin (n+1+L)=>gaussianBlockSplit (n+1) L u.val) :=
    (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe
  rw [Measure.map_map (gaussianBlockJoin_measurable (n+1) L) hm,
    Measure.map_map (gaussianBlockJoin_measurable (n+1) L) (cavitySphereBlockEmbed_measurable n L)] at h
  simpa only [Function.comp_def,gaussianBlockJoin_split,cavitySphereBlockEmbed_formula,
    cavityNormalizedVec,cavityRho] using h

lemma cavityShellProbability_integral (n L : ℕ) (F : Spin L→ℝ) :
    (∫ z : {z : Spin L // z∈cavityShell L},F z.val ∂cavityShellProbability n L)=
      ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))⁻¹*
        ∫ z in cavityShell L,F z ∂(cavitySphereLaw n L : Measure (Spin L)) := by
  unfold cavityShellProbability
  rw [integral_subtype_comap (cavityShell_measurable L)]
  simp only [ProbabilityTheory.cond,Measure.restrict_smul,Measure.restrict_restrict (cavityShell_measurable L),
    inter_self,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,Measure.real]

theorem cavity_actual_shell_restriction (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (F : NormalizedSpin (n+1+L)→ℝ) (hF : Measurable F) {A : ℝ} (hA : 0≤A)
    (hF0 : ∀ x,0≤F x) (hFA : ∀ x,F x≤A) :
    (cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L)*
      (∫ s,F (cavityShellSpinEmbedding n L s) ∂cavityShellBaseLaw n L)≤
        ∫ x,F x ∂unitSphereLaw (n+1+L) := by
  let := cavityShellBaseLaw_probability n L hp
  let := cavityShellProbability_probability n L hp
  obtain ⟨E,hE,hEF⟩ := (MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet :
    MeasurableSet (Metric.sphere (0:Spin (n+1+L)) 1))).exists_measurable_extend hF (fun _=>inferInstance)
  let W : Spin (n+1+L)→ℝ:=fun x=>max 0 (min A (E x))
  have hW : Measurable W:=measurable_const.max (measurable_const.min hE)
  have hW0 (x) : 0≤W x := le_max_left _ _
  have hWA (x) : W x≤A := max_le hA (min_le_left _ _)
  have hWF (x : NormalizedSpin (n+1+L)) : W x.val=F x := by
    have he : E x.val=F x := congrFun hEF x
    simp only [W,he,min_eq_right (hFA x),max_eq_right (hF0 x)]
  let G : NormalizedSpin (n+1)×Spin L→ℝ:=fun p=>W (cavityNormalizedVec (n+1) L p.1 p.2)
  have hG : Measurable G:=hW.comp (cavityNormalizedVec_measurable (n+1) L)
  have hi : Integrable G ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L)) := by
    apply Integrable.of_bound hG.aestronglyMeasurable A
    exact ae_of_all _ fun p=>by
      change ‖W (cavityNormalizedVec (n+1) L p.1 p.2)‖≤A
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hW0 _)] using hWA (cavityNormalizedVec (n+1) L p.1 p.2)
  have heq : (∫ x,F x ∂unitSphereLaw (n+1+L))=
      ∫ p,G p ∂(unitSphereLaw (n+1)).prod (cavitySphereLaw n L) := by
    calc
      _=∫ x,W x.val ∂unitSphereLaw (n+1+L) := integral_congr_ae (ae_of_all _ fun x=>(hWF x).symm)
      _=∫ x,W x ∂(unitSphereLaw (n+1+L)).map Subtype.val :=
        (integral_map measurable_subtype_coe.aemeasurable hW.aestronglyMeasurable).symm
      _=_ := by rw [unitSphere_cavityAmbient_law,integral_map (cavityNormalizedVec_measurable (n+1) L).aemeasurable hW.aestronglyMeasurable]
  rw [heq,integral_prod _ hi]
  have hsi : Integrable (fun s : CavityShellSpin n L=>F (cavityShellSpinEmbedding n L s))
      (cavityShellBaseLaw n L) := by
    apply Integrable.of_bound (hF.comp (cavityShellSpinEmbedding_measurable n L)).aestronglyMeasurable A
    exact ae_of_all _ fun s=>by
      change ‖F (cavityShellSpinEmbedding n L s)‖≤A
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 _)] using hFA (cavityShellSpinEmbedding n L s)
  rw [cavityShellBaseLaw,integral_prod _ hsi,←integral_const_mul]
  apply integral_mono_ae
  · exact hsi.integral_prod_left.const_mul _
  · exact hi.integral_prod_left
  filter_upwards [hi.prod_right_ae] with x hx
  have hs : (fun z : {z : Spin L // z∈cavityShell L}=>F (cavityShellSpinEmbedding n L (x,z)))=
      (fun z=>G (x,z.val)) := by
    funext z
    exact (hWF (cavityShellSpinEmbedding n L (x,z))).symm
  rw [hs]
  have hc:=cavityShellProbability_integral n L (fun z=>G (x,z))
  rw [hc]
  have hm : (cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L)≠0 :=
    ne_of_gt (ENNReal.toReal_pos hp (measure_ne_top _ _))
  rw [←mul_assoc,mul_inv_cancel₀ hm,one_mul]
  exact setIntegral_le_integral hx (ae_of_all _ fun z=>hW0 _)


lemma cavityShell_bulkHamiltonian (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (g : BulkMark (n+1+L)) (s : CavityShellSpin n L) :
    bulkHamiltonian (n+1+L) M f v a g (cavityShellSpinEmbedding n L s)=
      cavityShellPatternEnergy n L M f a s+inner ℝ (cavityShellFeature n L v s) g := by
  unfold bulkHamiltonian cavityShellPatternEnergy cavityShellFeature
  exact congrArg (fun y=> (∑ i, f (∑ j, a i j * (cavityShellSpinEmbedding n L s).val j))+
    inner ℝ y g) (ambientBulkFeature_eq (n+1+L) v (cavityShellSpinEmbedding n L s)).symm

lemma cavity_restriction_log_of_bounded (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (H : NormalizedSpin (n+1+L)→ℝ) (hH : Measurable H) {A : ℝ}
    (hA : 0≤A) (hB : ∀ x,|H x|≤A) :
    Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))+
      Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>H (cavityShellSpinEmbedding n L s)) 1)≤
      Real.log (tiltPartition (unitSphereLaw (n+1+L)) H 1) := by
  let := cavityShellBaseLaw_probability n L hp
  have hR := cavity_actual_shell_restriction n L hp
    (fun x=>Real.exp (H x)) hH.exp
    (Real.exp_pos A).le (fun _=>(Real.exp_pos _).le)
    (fun x=>Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x)))
  have hm : 0<(cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L) :=
    ENNReal.toReal_pos hp (measure_ne_top _ _)
  have hs := tilt_partition_pos (cavityShellBaseLaw n L)
    (hH.comp (cavityShellSpinEmbedding_measurable n L)) hA
    (fun s=>hB (cavityShellSpinEmbedding n L s)) 1
  simp only [tiltPartition,one_mul,Function.comp_apply] at hs
  have hh := Real.log_le_log (mul_pos hm hs) hR
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hs)] at hh
  simpa only [tiltPartition,one_mul] using hh

lemma cavity_actual_shell_log_restriction (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (g : BulkMark (n+1+L))
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))+
      Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>cavityShellPatternEnergy n L M f a s+inner ℝ (cavityShellFeature n L v s) g) 1)≤
      Real.log (tiltPartition (unitSphereLaw (n+1+L))
        (bulkHamiltonian (n+1+L) M f v a g) 1) := by
  have hH : Measurable (bulkHamiltonian (n+1+L) M f v a g) :=
    (bulkHamiltonian_section_measurable (n+1+L) M f v (a,g))
  have h := cavity_restriction_log_of_bounded n L hp
    (bulkHamiltonian (n+1+L) M f v a g) hH
    (add_nonneg (mul_nonneg (Nat.cast_nonneg M) (norm_nonneg f))
      (mul_nonneg (by unfold bulkFeatureBound; positivity) (norm_nonneg g)))
    (bulkHamiltonian_bound (n+1+L) M f v (a,g))
  simpa only [cavityShell_bulkHamiltonian] using h

lemma cavity_gaussian_log_integrable {I S : Type} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hHA : ∀ s,|H s|≤A) (hVB : ∀ s,‖V s‖≤B) :
    Integrable (fun g=>Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1))
      (stdGaussian (EuclideanSpace ℝ I)) := by
  apply Integrable.mono' ((integrable_const A).add
    ((IsGaussian.integrable_id (μ:=stdGaussian (EuclideanSpace ℝ I))).norm.const_mul B))
    (gaussianLogPartition_measurable_finite μ hH hV).aestronglyMeasurable
  exact ae_of_all _ fun g=>by
    rw [Real.norm_eq_abs]
    apply tilt_log_partition_bound μ (hH.add (hV.inner measurable_const))
      (add_nonneg hA (mul_nonneg hB (norm_nonneg _)))
    intro s
    apply (abs_add_le _ _).trans
    exact add_le_add (hHA s) ((abs_real_inner_le_norm (V s) g).trans
      (mul_le_mul_of_nonneg_right (hVB s) (norm_nonneg _)))

end SphericalPerceptronFreeEnergy
end

end OAI
