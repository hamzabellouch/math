import Mathlib
import OAI.Probability.IsingPerceptron.ActualQuenched

namespace OAI

/-! Deviation Rate. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval

def sourceDeviationRate (α C : ℝ) (j N : ℕ) : ℝ :=
  ((7/2)+4*sqrt (25/12+4*α*C^2)/(1/2)^(j+1)+20*(1/2)^(j+1))*(N:ℝ)^(-(1:ℝ)/8)

lemma sourceDeviationRate_tendsto (α C : ℝ) (j : ℕ) :
    Tendsto (sourceDeviationRate α C j) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (N:ℝ)^(-(1:ℝ)/8)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp tendsto_natCast_atTop_atTop using 1
    funext n
    simp only [Function.comp_apply]
    congr 1
    ring
  unfold sourceDeviationRate
  simpa only [mul_zero] using h.const_mul
    ((7/2)+4*sqrt (25/12+4*α*C^2)/(1/2)^(j+1)+20*(1/2)^(j+1))

lemma source_eta_eventually : ∀ᶠN : ℕ in atTop,(N:ℝ)^(-(1:ℝ)/8) ≤ 1/2 := by
  have h : Tendsto (fun N : ℕ => (N:ℝ)^(-(1:ℝ)/8)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp tendsto_natCast_atTop_atTop using 1
    funext n
    simp only [Function.comp_apply]
    congr 1
    ring
  exact h.eventually_le_const (by norm_num)

lemma scale_rate_identity {N : ℕ} (hN : 0<N) :
    sqrt (N:ℝ)/((N:ℝ)^(-(1:ℝ)/8)*(perturbationScale N)^2)=(N:ℝ)^(-(1:ℝ)/8) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  unfold perturbationScale
  rw [sqrt_eq_rpow,← rpow_natCast,← rpow_mul hn.le,← rpow_add hn,← rpow_sub hn]
  norm_num

lemma source_scale_inverse {N : ℕ} (hN : 0<N) :
    (perturbationScale N)⁻¹ ≤ (N:ℝ)^(-(1:ℝ)/8) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  unfold perturbationScale
  rw [← rpow_neg (Nat.cast_nonneg N)]
  exact rpow_le_rpow_of_exponent_le hn (by norm_num)

theorem source_rawTensor_deviation_rate {M N : ℕ} (hN : 0<N) {α C : ℝ} (hα : 0 ≤ α)
    (hM : (M:ℝ) ≤ α*N) {f : ℝ → ℝ} (hf : Measurable f) (hC : ∀z,|f z| ≤ C)
    (v : ℕ → ℝ) (hv : ∀j : Fin N,v (j.val+1)∈Icc (1/2:ℝ) (5/2))
    (j : Fin N) (hη : (N:ℝ)^(-(1:ℝ)/8) ≤ 1/2) :
    (∫u in (1:ℝ)..2,∫p,rawTensorDeviation (M:=M) hN f (perturbationScale N) v j u p
      ∂perturbedDisorderLaw M N)/(perturbationScale N)  ≤  sourceDeviationRate α C j.val N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : 0<perturbationScale N := rpow_pos_of_pos hn _
  have he : 0<(N:ℝ)^(-(1:ℝ)/8) := rpow_pos_of_pos hn _
  have hd : (0:ℝ)<(1/2)^(j.val+1) := by positivity
  have h := rawTensor_deviation_integral (M:=M) hN hf hC (perturbationScale N) hs v hv j he hη
  have hV : (25/12)*(perturbationScale N)^2+4*M*C^2 ≤ (25/12+4*α*C^2)*N := by
    have hrow := mul_le_mul_of_nonneg_right hM (sq_nonneg C)
    nlinarith [perturbationScale_sq_le hN]
  have hK : (0:ℝ) ≤ 25/12+4*α*C^2 := by positivity
  have hsqrt : sqrt ((25/12)*(perturbationScale N)^2+4*M*C^2) ≤ sqrt (25/12+4*α*C^2)*sqrt N := by
    simpa only [sqrt_mul hK] using sqrt_le_sqrt hV
  apply h.trans
  have hfirst : (7/2)/(perturbationScale N) ≤ (7/2)*(N:ℝ)^(-(1:ℝ)/8) := by
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (source_scale_inverse hN) (by norm_num : (0:ℝ) ≤ 7/2)
  have hsecond : 4*sqrt ((25/12)*(perturbationScale N)^2+4*M*C^2)/
      ((N:ℝ)^(-(1:ℝ)/8)*(perturbationScale N)^2*(1/2)^(j.val+1)) ≤ 
      (4*sqrt (25/12+4*α*C^2)/(1/2)^(j.val+1))*(N:ℝ)^(-(1:ℝ)/8) := by
    calc _  ≤  (4*(sqrt (25/12+4*α*C^2)*sqrt N))/
        ((N:ℝ)^(-(1:ℝ)/8)*(perturbationScale N)^2*(1/2)^(j.val+1)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (by positivity)
      _ = (4*sqrt (25/12+4*α*C^2)/(1/2)^(j.val+1))*
          (sqrt N/((N:ℝ)^(-(1:ℝ)/8)*(perturbationScale N)^2)) := by ring
      _ = _ := by rw [scale_rate_identity hN]
  unfold sourceDeviationRate
  nlinarith

lemma parameter_resampling_preserving {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (j : ℕ) :
    MeasurePreserving (fun p : (ℕ → X) × X => Function.update p.1 j p.2)
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod μ) (Measure.infinitePi (fun _ : ℕ => μ)) := by
  classical
  have hm : Measurable (fun p : (ℕ → X) × X => Function.update p.1 j p.2) := by fun_prop
  refine ⟨hm,Measure.eq_infinitePi _ ?_⟩
  intro s t ht
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hj : j∈s
  · have he : (fun p : (ℕ → X) × X => Function.update p.1 j p.2)⁻¹' (Set.pi s t)=
        (Set.pi (s.erase j) t) ×ˢ (t j) := by
      ext p
      simp only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Finset.mem_erase]
      constructor
      · intro h
        refine ⟨?_,?_⟩
        · intro i hi
          simpa only [Function.update_of_ne hi.1] using h i hi.2
        · simpa only [Function.update_self] using h j hj
      · rintro ⟨h,hu⟩ i hi
        by_cases hij : i=j
        · subst i
          simpa only [Function.update_self] using hu
        · simpa only [Function.update_of_ne hij] using h i ⟨hij,hi⟩
    rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht i)]
    exact Finset.prod_erase_mul s (fun i => μ (t i)) hj
  · have he : (fun p : (ℕ → X) × X => Function.update p.1 j p.2)⁻¹' (Set.pi s t)=
        (Set.pi s t) ×ˢ Set.univ := by
      ext p
      simp only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Set.mem_univ,and_true]
      congr! 2 with i
      rename_i hi
      rw [Function.update_of_ne (by intro he; exact hj (he ▸ hi))]
    rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht i),measure_univ,mul_one]

def parameterCoordinateLaw : Measure ℝ := volume.restrict (Ioc 1 2)

instance parameterCoordinateLaw_probability : IsProbabilityMeasure parameterCoordinateLaw := by
  constructor
  norm_num [parameterCoordinateLaw]

def sourceParameterLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => parameterCoordinateLaw)

instance sourceParameterLaw_probability : IsProbabilityMeasure sourceParameterLaw := by
  unfold sourceParameterLaw
  infer_instance

lemma parameterCoordinateLaw_mem : ∀ᵐu ∂parameterCoordinateLaw,u∈Icc (1:ℝ) 2 := by
  exact (ae_restrict_mem measurableSet_Ioc).mono (fun u hu => ⟨hu.1.le,hu.2⟩)

lemma sourceParameterLaw_mem : ∀ᵐv ∂sourceParameterLaw,∀j,v j∈Icc (1:ℝ) 2 := by
  rw [ae_all_iff]
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => parameterCoordinateLaw) j).quasiMeasurePreserving.ae parameterCoordinateLaw_mem

lemma integral_parameterCoordinateLaw (F : ℝ → ℝ) :
    (∫u,F u ∂parameterCoordinateLaw)=∫u in (1:ℝ)..2,F u := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
  rfl

instance perturbedDisorderLaw_probability (M N : ℕ) : IsProbabilityMeasure (perturbedDisorderLaw M N) := by
  unfold perturbedDisorderLaw
  infer_instance

def tensorMeanAt {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (j : Fin N)
    (v : ℕ → ℝ) (p : PerturbedDisorder M N) : ℝ :=
  rawTensorMean hN f s v j (v (j.val+1)) p

def tensorDeviationAt {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (j : Fin N)
    (v : ℕ → ℝ) (p : PerturbedDisorder M N) : ℝ :=
  rawTensorDeviation hN f s v j (v (j.val+1)) p

lemma tensorMeanAt_measurable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) :
    Measurable (fun p : (ℕ → ℝ) × PerturbedDisorder M N => tensorMeanAt hN f s j p.1 p.2) := by
  unfold tensorMeanAt rawTensorMean
  simp only [Function.update_eq_self]
  unfold fullTensorEnergy fullTensorCoefficient tensorAmplitude patternEnergy rowEvaluation
    selectedTensorObservable tensorPerturbation gaussianLinear
  apply finiteGibbs_measurable <;> intro x <;> fun_prop

lemma tensorDeviationAt_measurable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) :
    Measurable (fun p : (ℕ → ℝ) × PerturbedDisorder M N => tensorDeviationAt hN f s j p.1 p.2) := by
  have hm : Measurable (fun v => ∫q,tensorMeanAt (M:=M) hN f s j v q ∂perturbedDisorderLaw M N) :=
    (tensorMeanAt_measurable hN hf s j).stronglyMeasurable.integral_prod_right.measurable
  unfold tensorDeviationAt rawTensorDeviation
  change Measurable (fun p : (ℕ → ℝ) × PerturbedDisorder M N =>
    finiteGibbs (fun x => patternEnergy f p.2.2 x+
      fullTensorEnergy hN s (Function.update p.1 (j.val+1) (p.1 (j.val+1))) p.2.1 x)
      (fun x => |selectedTensorObservable hN j p.2.1 x-
        ∫q,tensorMeanAt hN f s j p.1 q ∂perturbedDisorderLaw M N|))
  simp only [Function.update_eq_self]
  apply finiteGibbs_measurable
  · intro x
    unfold patternEnergy rowEvaluation fullTensorEnergy fullTensorCoefficient tensorAmplitude
    fun_prop
  · intro x
    apply Measurable.abs
    apply Measurable.sub _ (hm.comp measurable_fst)
    unfold selectedTensorObservable tensorPerturbation gaussianLinear
    fun_prop

def tensorMajorant {N : ℕ} (hN : 0<N) (j : Fin N)
    (g : Fin (Fintype.card (FullTensorIndex N)) → ℝ) : ℝ :=
  ∑x : Spins N,|selectedTensorObservable hN j g x|

lemma tensorMajorant_memLp {N : ℕ} (hN : 0<N) (j : Fin N) :
    MemLp (tensorMajorant hN j) 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
  apply memLp_finsetSum
  intro x _
  apply MemLp.abs
  unfold selectedTensorObservable tensorPerturbation gaussianLinear
  apply memLp_finsetSum
  intro i _
  exact ((memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin (Fintype.card (FullTensorIndex N)) => gaussianReal 0 1)
      ((fullTensorEnumeration N).symm ⟨j,i⟩))).mul_const _

lemma tensorMeanAt_bound {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (j : Fin N)
    (v : ℕ → ℝ) (p : PerturbedDisorder M N) :
    |tensorMeanAt hN f s j v p| ≤ tensorMajorant hN j p.1 :=
  finiteGibbs_abs _ _ (finiteFunction_bound _)

lemma tensorMeanAt_integrable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) (v : ℕ → ℝ) :
    Integrable (tensorMeanAt hN f s j v) (perturbedDisorderLaw M N) := by
  apply (((tensorMajorant_memLp hN j).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num)).mono'
    (((tensorMeanAt_measurable hN hf s j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ fun p => tensorMeanAt_bound hN f s j v p

lemma tensorDeviationAt_bound {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) (v : ℕ → ℝ) (p : PerturbedDisorder M N) :
    |tensorDeviationAt hN f s j v p| ≤ tensorMajorant hN j p.1+
      ∫q : PerturbedDisorder M N,tensorMajorant hN j q.1 ∂perturbedDisorderLaw M N := by
  apply finiteGibbs_abs
  intro x
  rw [abs_abs]
  apply (abs_sub _ _).trans
  apply add_le_add (finiteFunction_bound _ x)
  calc
    _ ≤ ∫q,|tensorMeanAt hN f s j v q| ∂perturbedDisorderLaw M N := by
      simpa only [Real.norm_eq_abs,tensorMeanAt] using norm_integral_le_integral_norm (tensorMeanAt hN f s j v)
    _ ≤ _ := integral_mono (tensorMeanAt_integrable hN hf s j v).abs
      (((tensorMajorant_memLp hN j).comp_measurePreserving measurePreserving_fst).integrable (by norm_num))
      (tensorMeanAt_bound hN f s j v)

lemma tensorDeviationAt_integrable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) (v : ℕ → ℝ) :
    Integrable (tensorDeviationAt hN f s j v) (perturbedDisorderLaw M N) := by
  apply ((((tensorMajorant_memLp hN j).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num)).add (integrable_const _)).mono'
    (((tensorDeviationAt_measurable hN hf s j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply,id_eq] using tensorDeviationAt_bound hN hf s j v p

def meanTensorDeviation {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (j : Fin N)
    (v : ℕ → ℝ) : ℝ := ∫p,tensorDeviationAt hN f s j v p ∂perturbedDisorderLaw M N

lemma meanTensorDeviation_measurable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) : Measurable (meanTensorDeviation (M:=M) hN f s j) :=
  (tensorDeviationAt_measurable hN hf s j).stronglyMeasurable.integral_prod_right.measurable

lemma meanTensorDeviation_nonneg {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (j : Fin N)
    (v : ℕ → ℝ) : 0 ≤ meanTensorDeviation (M:=M) hN f s j v := by
  apply integral_nonneg
  intro p
  apply finiteGibbs_nonneg
  intro x
  exact abs_nonneg _

lemma meanTensorDeviation_bound {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) (v : ℕ → ℝ) :
    |meanTensorDeviation (M:=M) hN f s j v| ≤
      2*∫q : PerturbedDisorder M N,tensorMajorant hN j q.1 ∂perturbedDisorderLaw M N := by
  have hi : Integrable (fun q : PerturbedDisorder M N => tensorMajorant hN j q.1) (perturbedDisorderLaw M N) := ((tensorMajorant_memLp hN j).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num : (1:ENNReal)≤2)
  calc
    _ ≤ ∫p,|tensorDeviationAt hN f s j v p| ∂perturbedDisorderLaw M N := by
      simpa only [Real.norm_eq_abs,meanTensorDeviation] using norm_integral_le_integral_norm (tensorDeviationAt hN f s j v)
    _ ≤ ∫p,tensorMajorant hN j p.1+(∫q : PerturbedDisorder M N,tensorMajorant hN j q.1
        ∂perturbedDisorderLaw M N) ∂perturbedDisorderLaw M N :=
      integral_mono (tensorDeviationAt_integrable hN hf s j v).abs (hi.add (integrable_const _))
        (tensorDeviationAt_bound hN hf s j v)
    _ = _ := by rw [integral_add hi (integrable_const _)]; simp only [integral_const,probReal_univ,one_smul]; ring

lemma meanTensorDeviation_integrable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) (j : Fin N) :
    Integrable (meanTensorDeviation (M:=M) hN f s j) sourceParameterLaw :=
  (bounded_memLp sourceParameterLaw (meanTensorDeviation_measurable hN hf s j)
    (meanTensorDeviation_bound hN hf s j)).integrable (by norm_num)

lemma integral_resample_parameter {F : (ℕ → ℝ) → ℝ}
    (hF : Integrable F sourceParameterLaw) (j : ℕ) :
    (∫v,∫u,F (Function.update v j u) ∂parameterCoordinateLaw ∂sourceParameterLaw)=
      ∫v,F v ∂sourceParameterLaw := by
  have hp := parameter_resampling_preserving parameterCoordinateLaw j
  have hi := hp.integrable_comp_of_integrable hF
  have hi' : Integrable (Function.uncurry (fun v u => F (Function.update v j u)))
      (sourceParameterLaw.prod parameterCoordinateLaw) := hi
  rw [integral_integral hi']
  have he : Measure.map (fun p : (ℕ → ℝ) × ℝ => Function.update p.1 j p.2)
      (sourceParameterLaw.prod parameterCoordinateLaw)=sourceParameterLaw := hp.map_eq
  rw [← integral_map hp.measurable.aemeasurable]
  · rw [he]
  · simpa only [he] using hF.aestronglyMeasurable

lemma meanTensorDeviation_update {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (u : ℝ) :
    meanTensorDeviation (M:=M) hN f s j (Function.update v (j.val+1) u)=
      ∫p,rawTensorDeviation hN f s v j u p ∂perturbedDisorderLaw M N := by
  simp only [meanTensorDeviation,tensorDeviationAt,rawTensorDeviation,rawTensorMean,
    Function.update_self,Function.update_idem]

theorem source_parameter_deviation_rate {M N : ℕ} (hN : 0<N) {α C : ℝ} (hα : 0 ≤ α)
    (hM : (M:ℝ) ≤ α*N) {f : ℝ → ℝ} (hf : Measurable f) (hC : ∀z,|f z| ≤ C)
    (j : Fin N) (hη : (N:ℝ)^(-(1:ℝ)/8) ≤ 1/2) :
    (∫v,meanTensorDeviation (M:=M) hN f (perturbationScale N) j v ∂sourceParameterLaw)/
      perturbationScale N ≤ sourceDeviationRate α C j.val N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : 0<perturbationScale N := rpow_pos_of_pos hn _
  have hi := meanTensorDeviation_integrable (M:=M) hN hf (perturbationScale N) j
  have hp := parameter_resampling_preserving parameterCoordinateLaw (j.val+1)
  have hir := hp.integrable_comp_of_integrable hi
  rw [← integral_resample_parameter hi (j.val+1),← integral_div]
  have hi2 : Integrable (fun v =>
      (∫u,meanTensorDeviation (M:=M) hN f (perturbationScale N) j (Function.update v (j.val+1) u)
        ∂parameterCoordinateLaw)/perturbationScale N) sourceParameterLaw :=
    hir.integral_prod_left.div_const _
  have hbound : (∫v, (sourceDeviationRate α C j.val N : ℝ) ∂sourceParameterLaw)=
      sourceDeviationRate α C j.val N := by simp
  rw [← hbound]
  apply integral_mono_ae hi2 (integrable_const _)
  filter_upwards [sourceParameterLaw_mem] with v hv
  rw [integral_parameterCoordinateLaw]
  simp_rw [meanTensorDeviation_update]
  apply source_rawTensor_deviation_rate hN hα hM hf hC v _ j hη
  intro k
  constructor <;> linarith [(hv (k.val+1)).1,(hv (k.val+1)).2]

def sourceDeviation (α : ℝ) (f : ℝ → ℝ) (j N : ℕ) (v : ℕ → ℝ) : ℝ :=
  if h : j<N then
    meanTensorDeviation (M:=patternCount α N-2) (Nat.lt_of_le_of_lt (Nat.zero_le j) h)
      f (perturbationScale N) ⟨j,h⟩ v/perturbationScale N
  else 0

lemma sourceDeviation_measurable (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (j N : ℕ) :
    Measurable (sourceDeviation α f j N) := by
  unfold sourceDeviation
  split_ifs with h
  · exact (meanTensorDeviation_measurable _ hf _ _).div_const _
  · exact measurable_const

lemma sourceDeviation_integrable (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (j N : ℕ) :
    Integrable (sourceDeviation α f j N) sourceParameterLaw := by
  unfold sourceDeviation
  split_ifs with h
  · exact (meanTensorDeviation_integrable _ hf _ _).div_const _
  · exact integrable_const _

lemma sourceDeviation_nonneg (α : ℝ) (f : ℝ → ℝ) (j N : ℕ) (v : ℕ → ℝ) :
    0 ≤ sourceDeviation α f j N v := by
  unfold sourceDeviation
  split_ifs with h
  · exact div_nonneg (meanTensorDeviation_nonneg _ _ _ _ _) (rpow_nonneg (Nat.cast_nonneg N) _)
  · exact le_rfl

theorem source_integrated_deviation_tendsto (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C) (j : ℕ) :
    Tendsto (fun N => ∫v,sourceDeviation α f j N v ∂sourceParameterLaw) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N => integral_nonneg (sourceDeviation_nonneg α f j N)))
    _ (sourceDeviationRate_tendsto α C j)
  filter_upwards [eventually_gt_atTop j,source_eta_eventually] with N hN hη
  have hn : (0:ℝ)<N := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j) hN)
  have hM : ((patternCount α N-2:ℕ):ℝ) ≤ α*N :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (mul_nonneg hα hn.le))
  simp only [sourceDeviation,dite_eq_left hN,integral_div]
  exact source_parameter_deviation_rate _ hα hM hf hC ⟨j,hN⟩ hη

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open Filter Set
open scoped BigOperators Topology
open Classical

def slowDiagonal (b : ℕ → ℕ → ℝ) (N : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∀m,N ≤ m →
    ∑j ∈ Finset.range k,b j m ≤ 1/((k:ℝ)+1)) N

lemma slowDiagonal_le (b : ℕ → ℕ → ℝ) (N : ℕ) : slowDiagonal b N ≤ N :=
  Nat.findGreatest_le N

lemma slowDiagonal_mono (b : ℕ → ℕ → ℝ) : Monotone (slowDiagonal b) := by
  intro M N hMN
  exact Nat.findGreatest_mono (fun k hk m hm => hk m (hMN.trans hm)) hMN

lemma slowDiagonal_bound (b : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑j ∈ Finset.range (slowDiagonal b N),b j N ≤ 1/((slowDiagonal b N:ℝ)+1) := by
  have h0 : ∀m,N ≤ m → ∑j ∈ Finset.range 0,b j m ≤ 1/((0:ℝ)+1) := by simp
  have hs : ∀m,N ≤ m →
      ∑j ∈ Finset.range (slowDiagonal b N),b j m ≤ 1/((slowDiagonal b N:ℝ)+1) :=
    Nat.findGreatest_spec (P:=fun k => ∀m,N ≤ m →
      ∑j ∈ Finset.range k,b j m ≤ 1/((k:ℝ)+1)) (Nat.zero_le N) (by simpa only [Nat.cast_zero] using h0)
  exact hs N le_rfl

lemma slowDiagonal_tendsto {b : ℕ → ℕ → ℝ}
    (hb : ∀j,Tendsto (b j) atTop (𝓝 0)) :
    Tendsto (slowDiagonal b) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  have hsum : Tendsto (fun N => ∑j ∈ Finset.range k,b j N) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range k) (fun j _ => hb j)
  have hp : (0:ℝ)<1/((k:ℝ)+1) := by positivity
  obtain ⟨n,hn⟩ := eventually_atTop.mp (hsum.eventually (gt_mem_nhds hp))
  filter_upwards [eventually_ge_atTop (max k n)] with N hN
  apply Nat.le_findGreatest (le_trans (le_max_left _ _) hN)
  intro m hm
  exact (hn m ((le_max_right _ _).trans (hN.trans hm))).le

lemma slowDiagonal_sum_tendsto {b : ℕ → ℕ → ℝ}
    (hb0 : ∀j N,0 ≤ b j N) (hb : ∀j,Tendsto (b j) atTop (𝓝 0)) :
    Tendsto (fun N => ∑j ∈ Finset.range (slowDiagonal b N),b j N) atTop (𝓝 0) := by
  apply squeeze_zero (fun N => Finset.sum_nonneg (fun j _ => hb0 j N))
    (slowDiagonal_bound b)
  exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (slowDiagonal_tendsto hb)

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology

def sourceGoodCutoff (α : ℝ) (f : ℝ → ℝ) : ℕ → ℕ :=
  slowDiagonal (fun j N => ∫v,sourceDeviation α f j N v ∂sourceParameterLaw)

def sourceGoodError (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑j ∈ Finset.range (sourceGoodCutoff α f N),
    ∫v,sourceDeviation α f j N v ∂sourceParameterLaw

def sourceGoodTolerance (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  sqrt (sourceGoodError α f N)+1/(N:ℝ)

def sourceGoodParameters (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : Set (ℕ → ℝ) :=
  {v | ∀j,v j∈Icc (1:ℝ) 2} ∩
  {v | ∑j ∈ Finset.range (sourceGoodCutoff α f N),sourceDeviation α f j N v ≤
    sourceGoodTolerance α f N}

lemma sourceGoodCutoff_le (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : sourceGoodCutoff α f N ≤ N :=
  slowDiagonal_le _ _

lemma sourceGoodCutoff_monotone (α : ℝ) (f : ℝ → ℝ) : Monotone (sourceGoodCutoff α f) :=
  slowDiagonal_mono _

lemma sourceGoodCutoff_tendsto (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C) :
    Tendsto (sourceGoodCutoff α f) atTop atTop :=
  slowDiagonal_tendsto (source_integrated_deviation_tendsto α hα hf hC)

lemma sourceGoodError_nonneg (α : ℝ) (f : ℝ → ℝ) (N : ℕ) : 0 ≤ sourceGoodError α f N :=
  Finset.sum_nonneg (fun j _ => integral_nonneg (sourceDeviation_nonneg α f j N))

lemma sourceGoodError_tendsto (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C) :
    Tendsto (sourceGoodError α f) atTop (𝓝 0) :=
  slowDiagonal_sum_tendsto (fun j N => integral_nonneg (sourceDeviation_nonneg α f j N))
    (source_integrated_deviation_tendsto α hα hf hC)

lemma sourceGoodTolerance_pos (α : ℝ) (f : ℝ → ℝ) {N : ℕ} (hN : 0<N) :
    0<sourceGoodTolerance α f N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  exact add_pos_of_nonneg_of_pos (sqrt_nonneg _) (one_div_pos.mpr hn)

lemma sourceGoodTolerance_tendsto (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C) :
    Tendsto (sourceGoodTolerance α f) atTop (𝓝 0) := by
  have he := sourceGoodError_tendsto α hα hf hC
  have hs := continuous_sqrt.continuousAt.tendsto.comp he
  change Tendsto (fun N => sqrt (sourceGoodError α f N)+1/(N:ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def,sqrt_zero,zero_add] using hs.add
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))

lemma sourceGoodParameters_measurable (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (N : ℕ) :
    MeasurableSet (sourceGoodParameters α f N) := by
  apply MeasurableSet.inter
  · have hm : MeasurableSet (⋂j : ℕ,(fun v : ℕ → ℝ => v j)⁻¹' Icc (1:ℝ) 2) :=
      MeasurableSet.iInter (fun j => measurableSet_Icc.preimage (measurable_pi_apply j))
    convert hm using 1
    ext v
    simp only [mem_ofPred_eq,mem_iInter,mem_preimage]
  · exact measurableSet_le (Finset.measurable_sum _ (fun j _ => sourceDeviation_measurable α hf j N))
      measurable_const

lemma sourceGoodParameters_bad_bound (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {N : ℕ} (hN : 0<N) :
    sourceParameterLaw.real (sourceGoodParameters α f N)ᶜ ≤
      sourceGoodError α f N/sourceGoodTolerance α f N := by
  let A := fun v => ∑j ∈ Finset.range (sourceGoodCutoff α f N),sourceDeviation α f j N v
  have hA : Integrable A sourceParameterLaw :=
    integrable_finsetSum _ (fun j _ => sourceDeviation_integrable α hf j N)
  have hA0 : ∀v,0 ≤ A v := fun v =>
    Finset.sum_nonneg (fun j _ => sourceDeviation_nonneg α f j N v)
  have he : (∫v,A v ∂sourceParameterLaw)=sourceGoodError α f N := by
    exact integral_finsetSum _ (fun j _ => sourceDeviation_integrable α hf j N)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hA0) hA
    (sourceGoodTolerance α f N)
  rw [he] at hmark
  have hset : sourceParameterLaw (sourceGoodParameters α f N)ᶜ=
      sourceParameterLaw {v | sourceGoodTolerance α f N<A v} := by
    apply measure_congr
    filter_upwards [sourceParameterLaw_mem] with v hv
    apply propext
    change (¬((∀j,v j∈Icc (1:ℝ) 2) ∧ A v ≤ sourceGoodTolerance α f N)) ↔
      sourceGoodTolerance α f N<A v
    simp only [hv,forall_const,true_and,not_le]
  have hle : sourceParameterLaw.real (sourceGoodParameters α f N)ᶜ ≤
      sourceParameterLaw.real {v | sourceGoodTolerance α f N ≤ A v} := by
    rw [measureReal_def,hset]
    exact measureReal_mono (show {v | sourceGoodTolerance α f N<A v} ⊆
      {v | sourceGoodTolerance α f N ≤ A v} from
        fun v hv => (show sourceGoodTolerance α f N<A v from hv).le)
  exact (le_div_iff₀ (sourceGoodTolerance_pos α f hN)).mpr
    ((mul_le_mul_of_nonneg_right hle (sourceGoodTolerance_pos α f hN).le).trans
      (by simpa only [mul_comm] using hmark))

lemma sourceGoodParameters_bad_sqrt (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {N : ℕ} (hN : 0<N) :
    sourceParameterLaw.real (sourceGoodParameters α f N)ᶜ ≤ sqrt (sourceGoodError α f N) := by
  apply (sourceGoodParameters_bad_bound α hf hN).trans
  apply (div_le_iff₀ (sourceGoodTolerance_pos α f hN)).mpr
  have hs := sq_sqrt (sourceGoodError_nonneg α f N)
  have hp : 0 ≤ sqrt (sourceGoodError α f N)*(1/(N:ℝ)) := by positivity
  dsimp [sourceGoodTolerance]
  nlinarith

lemma sourceGoodParameters_probability (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C) :
    Tendsto (fun N => sourceParameterLaw.real (sourceGoodParameters α f N)) atTop (𝓝 1) := by
  have hb : Tendsto (fun N => sourceParameterLaw.real (sourceGoodParameters α f N)ᶜ)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N => ENNReal.toReal_nonneg))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact sourceGoodParameters_bad_sqrt α hf hN
    · simpa only [Function.comp_def,sqrt_zero] using
        continuous_sqrt.continuousAt.tendsto.comp (sourceGoodError_tendsto α hα hf hC)
  have he (N : ℕ) : sourceParameterLaw.real (sourceGoodParameters α f N)=
      1-sourceParameterLaw.real (sourceGoodParameters α f N)ᶜ := by
    rw [measureReal_compl (sourceGoodParameters_measurable α hf N)]
    simp
  simp_rw [he]
  simpa using tendsto_const_nhds.sub hb

lemma sourceGoodParameters_uniform {α : ℝ} {f : ℝ → ℝ} {j N : ℕ}
    (hj : j<sourceGoodCutoff α f N) {v : ℕ → ℝ} (hv : v∈sourceGoodParameters α f N) :
    sourceDeviation α f j N v ≤ sourceGoodTolerance α f N := by
  exact (Finset.single_le_sum (fun k _ => sourceDeviation_nonneg α f k N v)
    (Finset.mem_range.mpr hj)).trans hv.2

theorem source_good_parameters (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C) :
    (Monotone (sourceGoodCutoff α f) ∧ Tendsto (sourceGoodCutoff α f) atTop atTop) ∧
    Tendsto (fun N => sourceParameterLaw.real (sourceGoodParameters α f N)) atTop (𝓝 1) ∧
    ∀v : ℕ → (ℕ → ℝ),(∀ᶠN in atTop,v N∈sourceGoodParameters α f N) →
      ∀j,Tendsto (fun N => sourceDeviation α f j N (v N)) atTop (𝓝 0) := by
  refine ⟨⟨sourceGoodCutoff_monotone α f,sourceGoodCutoff_tendsto α hα hf hC⟩,
    sourceGoodParameters_probability α hα hf hC,?_⟩
  intro v hv j
  apply squeeze_zero' (Eventually.of_forall (fun N => sourceDeviation_nonneg α f j N (v N)))
    _ (sourceGoodTolerance_tendsto α hα hf hC)
  filter_upwards [hv,(sourceGoodCutoff_tendsto α hα hf hC).eventually (eventually_gt_atTop j)] with N hv hj
  exact sourceGoodParameters_uniform hj hv

end IsingPerceptron.Main

end

end OAI
