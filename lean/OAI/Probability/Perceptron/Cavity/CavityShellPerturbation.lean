import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityShellLimit
import OAI.Probability.Perceptron.Cavity.CavityGeometry

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal BoundedContinuousFunction

abbrev CavityShellSpin (n L : ℕ) := NormalizedSpin (n+1) × {z : Spin L // z∈cavityShell L}

def cavityShellFeature (n L : ℕ) (v : ℕ→ℝ) (s : CavityShellSpin n L) : BulkMark (n+1+L) :=
  ambientBulkFeature (n+1+L) v (cavityNormalizedVec (n+1) L s.1 s.2.val)

lemma cavityRho_measurable (N L : ℕ) : Measurable (cavityRho N L) := by
  unfold cavityRho
  fun_prop

lemma cavityNormalizedVec_measurable (N L : ℕ) :
    Measurable (fun p : NormalizedSpin N×Spin L=>cavityNormalizedVec N L p.1 p.2) := by
  unfold cavityNormalizedVec
  apply (gaussianBlockJoin_measurable N L).comp
  exact (((cavityRho_measurable N L).comp measurable_snd).smul measurable_fst.subtype_val).prodMk
    (measurable_snd.const_smul ((Real.sqrt (N+L:ℕ))⁻¹))

lemma ambientBulkFeature_measurable_comp {S : Type*} [MeasurableSpace S]
    (N : ℕ) (v : ℕ→ℝ) {u : S→Spin N} (hu : Measurable u) :
    Measurable (fun s=>ambientBulkFeature N v (u s)) :=
  (ambientBulkFeature_contDiff N v).continuous.measurable.comp hu

lemma cavityShellFeature_measurable (n L : ℕ) (v : ℕ→ℝ) :
    Measurable (cavityShellFeature n L v) := by
  unfold cavityShellFeature
  apply ambientBulkFeature_measurable_comp
  exact (cavityNormalizedVec_measurable (n+1) L).comp
    (f:=fun s : CavityShellSpin n L=>(s.1,s.2.val))
    (measurable_fst.prodMk measurable_snd.subtype_val)

lemma cavityShellFeature_norm (n L : ℕ) (v : ℕ→ℝ) (s : CavityShellSpin n L) :
    ‖cavityShellFeature n L v s‖=bulkFeatureBound (n+1+L) v := by
  have hz : ‖s.2.val‖^2≤(n+1+L:ℕ) := s.2.prop.2.trans (by
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) n])
  let u : NormalizedSpin (n+1+L) := ⟨cavityNormalizedVec (n+1) L s.1 s.2.val,by
    simpa only [Metric.mem_sphere,dist_zero_right] using
      cavityNormalizedVec_norm _ _ s.1 s.2.val (by omega) hz⟩
  change ‖ambientBulkFeature _ v u.val‖=_
  rw [ambientBulkFeature_eq,bulkFeature_norm]

theorem cavity_shell_perturbation_comparison (n L : ℕ) (v : ℕ→ℝ)
    (μ : Measure (CavityShellSpin n L)) [IsProbabilityMeasure μ]
    {H : CavityShellSpin n L→ℝ} (hH : Measurable H)
    {A C : ℝ} (hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
    (hv : ∀ j,|v (j+1)|≤C) :
    |(∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (cavityShellFeature n L v s) g) 1)
        ∂stdGaussian (BulkMark (n+1+L)))-
      ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (bulkFeature (n+1) v s.1) g) 1)
        ∂stdGaussian (BulkMark (n+1))|≤
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1)) := by
  let B := bulkFeatureBound (n+1) v+bulkFeatureBound (n+1+L) v
  have hB1 : 0≤bulkFeatureBound (n+1) v := Real.sqrt_nonneg _
  have hB2 : 0≤bulkFeatureBound (n+1+L) v := Real.sqrt_nonneg _
  apply independentGaussian_covariance_comparison μ hH
    ((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst)
    (cavityShellFeature_measurable n L v) hA
    (C:=B) (by dsimp [B]; positivity) hHA
  · intro s
    simp only [Function.comp_apply,bulkFeature_norm]
    exact le_add_of_nonneg_right hB2
  · intro s
    rw [cavityShellFeature_norm]
    exact le_add_of_nonneg_left hB1
  · exact cavityBulkCovarianceError_nonneg _ _ _ (by positivity)
  · intro x y
    exact cavityNormalizedVec_covariance n L v C hC hv x.1 y.1 x.2.val y.2.val x.2.prop.2 y.2.prop.2

lemma cavity_shell_perturbation_error_tendsto (L : ℕ) (C : ℝ) :
    Tendsto (fun n=>Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1))) atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (cavityBulkCovarianceError_tendsto L C (by positivity : 0≤3*((L:ℝ)+1))).const_mul Real.pi

def cavityShellProbability (n L : ℕ) : Measure {z : Spin L // z∈cavityShell L} :=
  (cond (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)).comap Subtype.val

lemma cavityShellProbability_probability (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    IsProbabilityMeasure (cavityShellProbability n L) := by
  let ν := (cavitySphereLaw n L : Measure (Spin L))
  let := cond_isProbabilityMeasure (μ:=ν) hp
  apply (MeasurableEmbedding.subtype_coe (cavityShell_measurable L)).isProbabilityMeasure_comap
  simp only [Subtype.range_coe]
  apply (mem_ae_iff_prob_eq_one (cavityShell_measurable L)).mpr
  exact cond_apply_self hp (measure_ne_top _ _)

def cavityShellBaseLaw (n L : ℕ) : Measure (CavityShellSpin n L) :=
  (unitSphereLaw (n+1)).prod (cavityShellProbability n L)

lemma cavityShellBaseLaw_probability (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    IsProbabilityMeasure (cavityShellBaseLaw n L) := by
  let := cavityShellProbability_probability n L hp
  unfold cavityShellBaseLaw
  infer_instance

lemma cavityShell_probability_eventually (k : ℕ) :
    ∀ᶠ n in atTop, (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0 := by
  have he := (cavitySphereLaw_shell_tendsto k).eventually (lt_mem_nhds (cavityShellMass_pos k))
  filter_upwards [he] with n hn
  exact ne_of_gt (ENNReal.toReal_pos_iff.mp hn).1

def cavityShellSpinEmbedding (n L : ℕ) (s : CavityShellSpin n L) : NormalizedSpin (n+1+L) :=
  ⟨cavityNormalizedVec (n+1) L s.1 s.2.val,by
    have hz : ‖s.2.val‖^2≤(n+1+L:ℕ) := s.2.prop.2.trans (by
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n])
    simpa only [Metric.mem_sphere,dist_zero_right] using
      cavityNormalizedVec_norm _ _ s.1 s.2.val (by omega) hz⟩

lemma cavityShellSpinEmbedding_measurable (n L : ℕ) : Measurable (cavityShellSpinEmbedding n L) := by
  apply Measurable.subtype_mk
  exact (cavityNormalizedVec_measurable (n+1) L).comp
    (f:=fun s : CavityShellSpin n L=>(s.1,s.2.val))
    (measurable_fst.prodMk measurable_snd.subtype_val)

def cavityShellPatternEnergy (n L M : ℕ) (f : ℝ→ᵇℝ) (a : Fin M→Fin (n+1+L)→ℝ)
    (s : CavityShellSpin n L) : ℝ :=
  normalizedPatternEnergy (n+1+L) M f a (cavityShellSpinEmbedding n L s)

lemma cavityShellPatternEnergy_measurable (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) : Measurable (cavityShellPatternEnergy n L M f a) := by
  exact (normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp
    (f:=fun s : CavityShellSpin n L=>(a,cavityShellSpinEmbedding n L s))
    (measurable_const.prodMk (cavityShellSpinEmbedding_measurable n L))

lemma cavityShellPatternEnergy_bound (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L M f a s|≤M*‖f‖ :=
  normalizedPatternEnergy_bound _ _ _ _ _

theorem cavity_true_shell_perturbation (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hv : ∀ j,|v (j+1)|≤C)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    |(∫ g,Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>cavityShellPatternEnergy n L M f a s+inner ℝ (cavityShellFeature n L v s) g) 1)
        ∂stdGaussian (BulkMark (n+1+L)))-
      ∫ g,Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>cavityShellPatternEnergy n L M f a s+inner ℝ (bulkFeature (n+1) v s.1) g) 1)
        ∂stdGaussian (BulkMark (n+1))|≤
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1)) := by
  let := cavityShellBaseLaw_probability n L hp
  exact cavity_shell_perturbation_comparison n L v (cavityShellBaseLaw n L)
    (cavityShellPatternEnergy_measurable n L M f a) (by positivity) hC
    (cavityShellPatternEnergy_bound n L M f a) hv

end SphericalPerceptronFreeEnergy
end

end OAI
