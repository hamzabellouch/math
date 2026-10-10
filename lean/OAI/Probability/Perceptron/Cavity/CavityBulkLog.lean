import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityBulkCoefficients

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavitySingleTest_bounds (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    Real.exp (-(d:ℝ)*‖f‖)≤cavitySingleTest n d f Λ hΛ z ∧
      cavitySingleTest n d f Λ hΛ z≤Λ*Real.exp ((d:ℝ)*‖f‖) := by
  rw [cavitySingleTest_apply,←Real.exp_sum]
  have hs : |∑ t : Fin d,f (z (Sum.inr t))|≤(d:ℝ)*‖f‖ := by
    calc
      _≤∑ t : Fin d,|f (z (Sum.inr t))| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _ : Fin d,‖f‖ := Finset.sum_le_sum fun t ht=>f.norm_coe_le_norm _
      _=_ := by simp
  have hF := le_min (one_le_sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i)))
    (Real.sqrt (n+1:ℕ))) hΛ
  constructor
  · calc
      _≤Real.exp (∑ t : Fin d,f (z (Sum.inr t))) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hs).1])
      _≤_ := by nlinarith [Real.exp_pos (∑ t : Fin d,f (z (Sum.inr t)))]
  · exact mul_le_mul (min_le_right _ _) (Real.exp_le_exp.mpr (abs_le.mp hs).2)
      (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)

abbrev CavityPartitionRange (d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) :=
  Icc (Real.exp (-(d:ℝ)*‖f‖)) (Λ*Real.exp ((d:ℝ)*‖f‖))

lemma cavityBulkPartition_mem (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    cavityBulkPartition n d m M f v Λ hΛ p∈CavityPartitionRange d f.f Λ := by
  let H:=bulkGibbsHamiltonian m M f.f v p.1
  have hmH : Measurable H := (bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left
  have he : Integrable (fun x=>Real.exp (1*H x)) (unitSphereLaw (m+1)) := by
    simpa only [one_mul,H,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v p.1
  let := tilt_law_probability_of_integrable (unitSphereLaw (m+1)) he
  let μ:=tiltLaw (unitSphereLaw (m+1)) H 1
  have hv : Measurable (cavityBulkFeature n d m M f p.1) :=
    (cavityBulkFeature_measurable n d m M f).of_uncurry_left
  have hm : Measurable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) := by
    apply (cavitySingleTest n d f.f Λ hΛ).measurable.comp
    exact cavity_rows_joint_measurable hv measurable_const
  have hi : Integrable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Λ*Real.exp ((d:ℝ)*‖f.f‖))
    filter_upwards [] with x
    have hb:=cavitySingleTest_bounds n d f.f Λ hΛ (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)
    rw [Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le hb.1)]
    exact hb.2
  unfold cavityBulkPartition
  rw [←tilt_law_integral_of_integrable (unitSphereLaw (m+1)) hmH he]
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-(d:ℝ)*‖f.f‖))) hi
        (fun x=>(cavitySingleTest_bounds n d f.f Λ hΛ _).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hi (integrable_const (Λ*Real.exp ((d:ℝ)*‖f.f‖)))
        (fun x=>(cavitySingleTest_bounds n d f.f Λ hΛ _).2)

def cavityBulkPartitionLaw (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    ProbabilityMeasure (CavityPartitionRange d f.f Λ) :=
  ⟨((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))).map
    (fun p=>⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩),
    (Measure.isProbabilityMeasure_map_iff
      ((cavityBulkPartition_measurable n d m M f v Λ hΛ).subtype_mk).aemeasurable).2 inferInstance⟩

lemma cavityBulkPartitionLaw_integral (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (F : ℝ→ℝ) (hF : Measurable F) :
    (∫ x,F x.val ∂(cavityBulkPartitionLaw n d m M f v Λ hΛ : Measure (CavityPartitionRange d f.f Λ)))=
      ∫ p,F (cavityBulkPartition n d m M f v Λ hΛ p)
        ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) :=
  integral_map ((cavityBulkPartition_measurable n d m M f v Λ hΛ).subtype_mk).aemeasurable
    (hF.comp measurable_subtype_coe).aestronglyMeasurable

lemma cavityBulkPartition_power_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) :
    Integrable (fun p=>cavityBulkPartition n d m M f v Λ hΛ p^r)
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound ((cavityBulkPartition_measurable n d m M f v Λ hΛ).pow_const r).aestronglyMeasurable
    ((Λ*Real.exp ((d:ℝ)*‖f.f‖))^r)
  filter_upwards [] with p
  have hb:=cavityBulkPartition_mem n d m M f v Λ hΛ p
  rw [norm_pow,Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le hb.1)]
  exact pow_le_pow_left₀ ((Real.exp_pos _).trans_le hb.1).le hb.2 r

lemma cavityBulkPartitionLaw_moment (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) :
    (∫ x,x.val^r ∂(cavityBulkPartitionLaw n d m M f v Λ hΛ : Measure (CavityPartitionRange d f.f Λ)))=
      cavityBulkMoment n d m M f v Λ hΛ r := by
  rw [cavityBulkPartitionLaw_integral n d m M f v Λ hΛ (fun x : ℝ=>x^r) (by fun_prop),
    integral_prod _ (cavityBulkPartition_power_integrable n d m M f v Λ hΛ r)]
  rfl

def cavityPartitionLogTest (d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) : CavityPartitionRange d f Λ→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x=>Real.log x.val,
    continuous_subtype_val.log (fun x=>ne_of_gt ((Real.exp_pos _).trans_le x.prop.1))⟩

def cavityBulkLog (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) : ℝ :=
  ∫ a,∫ y,Real.log (cavityBulkPartition n d m M f v Λ hΛ (a,y))
    ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∂bulkDisorderLaw (m+1) M

lemma cavityBulkPartitionLaw_log (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    (∫ x,Real.log x.val ∂(cavityBulkPartitionLaw n d m M f v Λ hΛ : Measure (CavityPartitionRange d f.f Λ)))=
      cavityBulkLog n d m M f v Λ hΛ := by
  rw [cavityBulkPartitionLaw_integral _ _ _ _ _ _ _ _ _ Real.measurable_log]
  change _=∫ a,∫ y,Real.log (cavityBulkPartition n d m M f v Λ hΛ (a,y)) ∂stdGaussian _ ∂_
  apply integral_prod
  apply Integrable.of_bound ((cavityBulkPartition_measurable n d m M f v Λ hΛ).log).aestronglyMeasurable
    ‖cavityPartitionLogTest d f.f Λ‖
  filter_upwards [] with p
  exact (cavityPartitionLogTest d f.f Λ).norm_coe_le_norm
    ⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩

theorem cavityBulkLog_tendsto (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (CavityPartitionRange d f.f Λ),
      Tendsto (fun j=>cavityBulkPartitionLaw n d (s j) (M (s j)) f (v (s j)) Λ hΛ) atTop (𝓝 η) ∧
      (∀ r,(∫ x,x.val^r ∂(η : Measure (CavityPartitionRange d f.f Λ)))=∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂ν) ∧
      Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ) atTop
        (𝓝 (∫ x,Real.log x.val ∂(η : Measure (CavityPartitionRange d f.f Λ)))) := by
  have hmom r := cavityBulkMoment_tendsto n d M f v Λ hΛ K hK s hlim r
  simp_rw [←cavityBulkPartitionLaw_moment] at hmom
  obtain ⟨η,hη,hm⟩:=compact_moment_limit _ _ hmom
  refine ⟨η,hη,hm,?_⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cavityPartitionLogTest d f.f Λ)).continuousAt.tendsto.comp hη
  simpa only [Function.comp_def,cavityPartitionLogTest,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
    cavityBulkPartitionLaw_log] using ht

lemma log_sub_le_div_sub {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Real.log a-Real.log b≤(a-b)/b := by
  have h:=Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  convert h using 1
  field_simp

lemma cavity_cap_tail {x Λ : ℝ} (hx : 0≤x) (hΛ : 0<Λ) :
    0≤x-min x Λ ∧ x-min x Λ≤x^2/Λ := by
  constructor
  · exact sub_nonneg.mpr (min_le_left _ _)
  · apply (le_div_iff₀ hΛ).mpr
    by_cases h : x≤Λ
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right (le_of_not_ge h)]; nlinarith

lemma cavity_capped_log_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W F : S→ℝ} {C Λ : ℝ}
    (hW : Measurable W) (hWC : ∀ x,|W x|≤C) (hF : MemLp F 2 μ)
    (hF1 : ∀ x,1≤F x) (hΛ : 1≤Λ) :
    let A:=∫ x,Real.exp (W x)*F x ∂μ
    let B:=∫ x,Real.exp (W x)*min (F x) Λ ∂μ
    0≤Real.log A-Real.log B ∧
      Real.log A-Real.log B≤Real.exp (2*C)/Λ*(∫ x,(F x)^2 ∂μ) := by
  dsimp only
  let G : S→ℝ:=fun x=>min (F x) Λ
  have hFp x : 0≤F x := (by norm_num : (0:ℝ)≤1).trans (hF1 x)
  have hGp x : 1≤G x := le_min (hF1 x) hΛ
  have hGb x : ‖G x‖≤Λ := by
    rw [Real.norm_eq_abs,abs_of_nonneg ((by norm_num : (0:ℝ)≤1).trans (hGp x))]
    exact min_le_right _ _
  have hGm : AEStronglyMeasurable G μ := (hF.aestronglyMeasurable.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hGi : Integrable G μ := Integrable.of_bound hGm Λ (ae_of_all _ hGb)
  have hFi := hF.integrable (by norm_num)
  have hF2 : Integrable (fun x=>(F x)^2) μ := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  have hWF : Integrable (fun x=>Real.exp (W x)*F x) μ := by
    apply (hFi.const_mul (Real.exp C)).mono' (hW.exp.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (hFp x)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2) (hFp x)
  have hWG : Integrable (fun x=>Real.exp (W x)*G x) μ := by
    apply (hGi.const_mul (Real.exp C)).mono' (hW.exp.aestronglyMeasurable.mul hGm)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg ((by norm_num : (0:ℝ)≤1).trans (hGp x))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2)
      ((by norm_num : (0:ℝ)≤1).trans (hGp x))
  have hBlo : Real.exp (-C)≤∫ x,Real.exp (W x)*G x ∂μ := by
    calc
      _=∫ _ : S,Real.exp (-C) ∂μ := by simp
      _≤_ := integral_mono (integrable_const _) hWG fun x=>by
        calc
          Real.exp (-C)≤Real.exp (W x) := Real.exp_le_exp.mpr (abs_le.mp (hWC x)).1
          _≤Real.exp (W x)*G x := by nlinarith [Real.exp_pos (W x),hGp x]
  have hBA : (∫ x,Real.exp (W x)*G x ∂μ)≤∫ x,Real.exp (W x)*F x ∂μ :=
    integral_mono hWG hWF fun x=>mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_pos _).le
  have hBp: 0<∫ x,Real.exp (W x)*G x ∂μ := (Real.exp_pos _).trans_le hBlo
  have hAp:=hBp.trans_le hBA
  have htail : (∫ x,Real.exp (W x)*F x ∂μ)-(∫ x,Real.exp (W x)*G x ∂μ)≤
      Real.exp C/Λ*(∫ x,(F x)^2 ∂μ) := by
    rw [←integral_sub hWF hWG,←integral_const_mul]
    apply integral_mono (hWF.sub hWG) (hF2.const_mul _)
    intro x
    have ht:=cavity_cap_tail (hFp x) ((by norm_num : (0:ℝ)<1).trans_le hΛ)
    calc
      _=Real.exp (W x)*(F x-G x)  := by simp only [Pi.sub_apply]; ring
      _≤Real.exp C*(F x-G x) := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2) ht.1
      _≤Real.exp C*((F x)^2/Λ) := mul_le_mul_of_nonneg_left ht.2 (Real.exp_pos _).le
      _=_ := by ring
  refine ⟨sub_nonneg.mpr (Real.log_le_log hBp hBA),?_⟩
  calc
    _≤((∫ x,Real.exp (W x)*F x ∂μ)-(∫ x,Real.exp (W x)*G x ∂μ))/
      (∫ x,Real.exp (W x)*G x ∂μ) := log_sub_le_div_sub hAp hBp
    _≤(Real.exp C/Λ*(∫ x,(F x)^2 ∂μ))/(Real.exp (-C)) :=
      (div_le_div_of_nonneg_right htail hBp.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg (div_nonneg (Real.exp_pos _).le (le_trans (by norm_num) hΛ))
          (integral_nonneg fun x=>sq_nonneg _)) (Real.exp_pos _) hBlo)
    _=_ := by rw [Real.exp_neg,div_inv_eq_mul,show 2*C=C+C by ring,Real.exp_add]; ring

end SphericalPerceptronFreeEnergy
end

end OAI
