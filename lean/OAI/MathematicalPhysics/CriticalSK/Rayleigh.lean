import OAI.MathematicalPhysics.CriticalSK.Cavity
import OAI.MathematicalPhysics.CriticalSK.Covariance

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

@[simp] lemma abs_spinValue (b : Bool) : |spinValue b| = 1 := by cases b <;> norm_num [spinValue]

lemma cavityOverlapCoord_abs_le_one (i : Fin n) (x y : Spin n) : |cavityOverlapCoord i x y| ≤ 1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  rw [cavityOverlapCoord,abs_div,abs_of_pos hn,div_le_one hn]
  calc
    |∑ j ∈ Finset.univ.erase i, spinValue (x j)*spinValue (y j)| ≤ ∑ j ∈ Finset.univ.erase i, |spinValue (x j)*spinValue (y j)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ)-1 := by
      simp only [abs_mul,abs_spinValue,mul_one,Finset.sum_const,nsmul_eq_mul,mul_one]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]
    _ ≤ (n:ℝ) := by linarith

lemma cavityNormalization_join (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) :
    cavityNormalization ((cavitySplit i).symm (u,v)) i =
      coshMixture (gibbs ((cavitySplit i).symm (0,v))) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) u := by
  simp only [cavityNormalization,delete_cavityJoin,mean,coshMixture,localField_cavityJoin,gaussianLinear]

lemma cavityOverlap_join (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) :
    cavityOverlap ((cavitySplit i).symm (u,v)) i =
      ∑ x, ∑ y, gibbs ((cavitySplit i).symm (0,v)) x*gibbs ((cavitySplit i).symm (0,v)) y*cavityOverlapCoord i x y^2 := by
  simp only [cavityOverlap,delete_cavityJoin,mean,Finset.mul_sum,mul_assoc]

lemma incident_variance_bound (i : Fin n) : (n:ℝ)⁻¹*((n:ℝ)-1) ≤ 1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  calc
    _ ≤ (n:ℝ)⁻¹*(n:ℝ) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hn.le)
    _ = 1 := inv_mul_cancel₀ hn.ne'

lemma incident_scaled_product (i : Fin n) (x y : Spin n) :
    (n:ℝ)⁻¹*(∑ e : Incident i, incidentCoeff i x e.val*incidentCoeff i y e.val) = cavityOverlapCoord i x y := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  rw [incident_coeff_product,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

lemma cavity_conditional_mean (i : Fin n) (v : Nonincident i → ℝ) :
    Integrable (fun u => cavityNormalization ((cavitySplit i).symm (u,v)) i) (incidentLaw i) ∧
    (∫ u, cavityNormalization ((cavitySplit i).symm (u,v)) i ∂incidentLaw i) = Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2) := by
  change Integrable (fun u => cavityNormalization ((cavitySplit i).symm (u,v)) i) (gaussianScalarPi (n:ℝ≥0)⁻¹) ∧ _
  simp_rw [cavityNormalization_join]
  refine ⟨coshMixture_integrable (n:ℝ≥0)⁻¹ (gibbs ((cavitySplit i).symm (0,v))) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val), ?_⟩
  change (∫ u, coshMixture (gibbs ((cavitySplit i).symm (0,v))) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) u ∂gaussianScalarPi (n:ℝ≥0)⁻¹) = _

  simpa only [NNReal.coe_inv,NNReal.coe_natCast] using coshMixture_integral (n:ℝ≥0)⁻¹ (gibbs_sum _) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) (incident_coeff_square i)

lemma cavity_conditional_pow (i : Fin n) (v : Nonincident i → ℝ) (m : ℕ) :
    Integrable (fun u => cavityNormalization ((cavitySplit i).symm (u,v)) i^m) (incidentLaw i) ∧
    (∫ u, cavityNormalization ((cavitySplit i).symm (u,v)) i^m ∂incidentLaw i) ≤ 2*Real.exp ((m:ℝ)^2/2) := by
  have hh := coshMixture_pow_integrable_bound (n:ℝ≥0)⁻¹ (gibbs_nonneg ((cavitySplit i).symm (0,v))) (gibbs_sum _) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) (incident_coeff_square i) m
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at hh
  simp_rw [cavityNormalization_join]
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (incident_variance_bound i) (sq_nonneg (m:ℝ))]

lemma cavity_conditional_variance (i : Fin n) (v : Nonincident i → ℝ) :
    Integrable (fun u => (cavityNormalization ((cavitySplit i).symm (u,v)) i-Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2))^2) (incidentLaw i) ∧
    (∫ u, (cavityNormalization ((cavitySplit i).symm (u,v)) i-Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2))^2 ∂incidentLaw i) ≤
      Real.exp 1*(Real.exp 1-1)*cavityOverlap ((cavitySplit i).symm (0,v)) i := by
  have hc (x y : Spin n) : |((n:ℝ≥0)⁻¹:ℝ)*(∑ e : Incident i, incidentCoeff i x e.val*incidentCoeff i y e.val)| ≤ 1 := by
    simpa only [NNReal.coe_inv,NNReal.coe_natCast,incident_scaled_product] using cavityOverlapCoord_abs_le_one i x y
  have hh := coshMixture_centered_integrable_bound (n:ℝ≥0)⁻¹ (gibbs_nonneg ((cavitySplit i).symm (0,v))) (gibbs_sum _) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) (incident_coeff_square i) hc
  simp only [NNReal.coe_inv,NNReal.coe_natCast,incident_scaled_product] at hh
  simp_rw [← cavityNormalization_join] at hh
  rw [← cavityOverlap_join i 0 v] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (incident_variance_bound i)) (by linarith [Real.add_one_le_exp 1])) (cavityOverlap_nonneg _ i)

lemma deleteDisorder_continuous (i : Fin n) : Continuous (fun W : Disorder n => deleteDisorder W i) := by
  apply continuous_pi
  intro e
  by_cases he : e.val.1=i ∨ e.val.2=i
  · simp only [deleteDisorder,ite_eq_left he]; exact continuous_const
  · simp only [deleteDisorder,ite_eq_right he]; exact continuous_apply e

lemma localField_continuous (i : Fin n) (x : Spin n) : Continuous (fun W : Disorder n => localField W i x) := by
  unfold localField
  fun_prop

lemma cavityNormalization_continuous (i : Fin n) : Continuous (fun W : Disorder n => cavityNormalization W i) := by
  unfold cavityNormalization mean
  apply continuous_finsetSum
  intro x _
  exact ((gibbs_continuous x).comp (deleteDisorder_continuous i)).mul (Real.continuous_cosh.comp (localField_continuous i x))

lemma cavityOverlap_continuous (i : Fin n) : Continuous (fun W : Disorder n => cavityOverlap W i) := by
  unfold cavityOverlap mean
  apply continuous_finsetSum
  intro x _
  apply ((gibbs_continuous x).comp (deleteDisorder_continuous i)).mul
  apply continuous_finsetSum
  intro y _
  exact ((gibbs_continuous y).comp (deleteDisorder_continuous i)).mul continuous_const

lemma cavity_event_identity (i : Fin n) {E : Set (Disorder n)} (hE : MeasurableSet E) :
    (disorderLaw n).real E = ∫ v, (incidentLaw i).real {u | (cavitySplit i).symm (u,v) ∈ E} ∂nonincidentLaw i :=
  preserving_product_event_real _ _ _ _ (cavitySplit_preserving i).symm hE

lemma cavity_conditional_tail (i : Fin n) (v : Nonincident i → ℝ) {b : ℝ} (hb : 0 < b) (m : ℕ) :
    (incidentLaw i).real {u | b ≤ cavityNormalization ((cavitySplit i).symm (u,v)) i} ≤ 2*Real.exp ((m:ℝ)^2/2)/b^m := by
  obtain ⟨hi,hh⟩ := cavity_conditional_pow i v m
  have ht := integral_dominates_event (E := {u | b ≤ cavityNormalization ((cavitySplit i).symm (u,v)) i})
    (hi.div_const (b^m)) (fun u => div_nonneg (pow_nonneg (by linarith [cavityNormalization_ge_one ((cavitySplit i).symm (u,v)) i]) _) (pow_nonneg hb.le _))
    (fun u hu => by
      apply (le_div_iff₀ (pow_pos hb _)).mpr
      rw [one_mul]
      exact pow_le_pow_left₀ hb.le hu _)
  rw [integral_div] at ht
  exact ht.trans (div_le_div_of_nonneg_right hh (pow_nonneg hb.le _))

lemma cavity_tail (i : Fin n) {b : ℝ} (hb : 0 < b) (m : ℕ) :
    (disorderLaw n).real {W | b ≤ cavityNormalization W i} ≤ 2*Real.exp ((m:ℝ)^2/2)/b^m := by
  rw [cavity_event_identity i (measurableSet_le measurable_const (cavityNormalization_continuous i).measurable)]
  calc
    _ ≤ ∫ _v, 2*Real.exp ((m:ℝ)^2/2)/b^m ∂nonincidentLaw i :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg)) (integrable_const _) (ae_of_all _ (fun v => cavity_conditional_tail i v hb m))
    _ = _ := by simp

lemma all_cavity_tail {b : ℝ} (hb : 0 < b) (m : ℕ) :
    (disorderLaw n).real {W | ∃ i, b ≤ cavityNormalization W i} ≤ (n:ℝ)*(2*Real.exp ((m:ℝ)^2/2)/b^m) := by
  have he : {W : Disorder n | ∃ i, b ≤ cavityNormalization W i} = ⋃ i : Fin n, {W | b ≤ cavityNormalization W i} := by ext W; simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin n, (disorderLaw n).real {W | b ≤ cavityNormalization W i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2*Real.exp ((m:ℝ)^2/2)/b^m := Finset.sum_le_sum (fun i _ => cavity_tail i hb m)
    _ = _ := by simp

lemma cavity_conditional_clipped (i : Fin n) (v : Nonincident i → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (incidentLaw i).real {u | Real.exp 1+1 < cavityNormalization ((cavitySplit i).symm (u,v)) i ∧ cavityOverlap ((cavitySplit i).symm (u,v)) i ≤ r} ≤
      Real.exp 1*(Real.exp 1-1)*r := by
  have he (u : Incident i → ℝ) : cavityOverlap ((cavitySplit i).symm (u,v)) i = cavityOverlap ((cavitySplit i).symm (0,v)) i := by
    rw [cavityOverlap_join,cavityOverlap_join]
  by_cases hR : cavityOverlap ((cavitySplit i).symm (0,v)) i ≤ r
  · obtain ⟨hi,hh⟩ := cavity_conditional_variance i v
    have hm : Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith [incident_variance_bound i])
    have ht := integral_dominates_event (E := {u | Real.exp 1+1 < cavityNormalization ((cavitySplit i).symm (u,v)) i ∧ cavityOverlap ((cavitySplit i).symm (u,v)) i ≤ r}) hi (fun _ => sq_nonneg _) (fun u hu => by
      have hz := hu.1
      nlinarith [sq_nonneg (cavityNormalization ((cavitySplit i).symm (u,v)) i-Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2)-1)])
    exact ht.trans (hh.trans (mul_le_mul_of_nonneg_left hR (mul_nonneg (Real.exp_pos _).le (by linarith [Real.add_one_le_exp 1]))))
  · have hset : {u | Real.exp 1+1 < cavityNormalization ((cavitySplit i).symm (u,v)) i ∧ cavityOverlap ((cavitySplit i).symm (u,v)) i ≤ r} = ∅ := by
      ext u
      simp only [mem_ofPred_eq,he,mem_empty_iff_false,iff_false,not_and]
      exact fun _ => hR
    rw [hset,measureReal_empty]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith [Real.add_one_le_exp 1])) hr

lemma cavityClipped_measurable (i : Fin n) (r : ℝ) : MeasurableSet {W : Disorder n | Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r} :=
  (measurableSet_lt measurable_const (cavityNormalization_continuous i).measurable).inter (measurableSet_le (cavityOverlap_continuous i).measurable measurable_const)

lemma cavity_clipped (i : Fin n) {r : ℝ} (hr : 0 ≤ r) :
    (disorderLaw n).real {W | Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r} ≤ Real.exp 1*(Real.exp 1-1)*r := by
  rw [cavity_event_identity i (cavityClipped_measurable i r)]
  calc
    _ ≤ ∫ _v, Real.exp 1*(Real.exp 1-1)*r ∂nonincidentLaw i :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg)) (integrable_const _) (ae_of_all _ (fun v => cavity_conditional_clipped i v hr))
    _ = _ := by simp

noncomputable def cavityClippedCount (W : Disorder n) (r : ℝ) : ℝ :=
  ∑ i : Fin n, if Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r then 1 else 0

lemma cavityClippedCount_nonneg (W : Disorder n) (r : ℝ) : 0 ≤ cavityClippedCount W r := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma cavityClippedCount_integrable (r : ℝ) : Integrable (fun W : Disorder n => cavityClippedCount W r) (disorderLaw n) := by
  unfold cavityClippedCount
  apply integrable_finsetSum
  intro i _
  refine ((integrable_const (μ := disorderLaw n) (1:ℝ)).indicator (cavityClipped_measurable i r)).congr (ae_of_all _ ?_)
  intro W
  by_cases hW : Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r <;> simp [hW]

lemma cavityClippedCount_expectation {r : ℝ} (hr : 0 ≤ r) :
    (∫ W, cavityClippedCount W r ∂disorderLaw n) ≤ (n:ℝ)*(Real.exp 1*(Real.exp 1-1)*r) := by
  unfold cavityClippedCount
  rw [integral_finsetSum]
  · calc
      _ = ∑ i : Fin n, (disorderLaw n).real {W | Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r} := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Set.indicator, mem_ofPred_eq, Pi.one_apply] using integral_indicator_one (μ := disorderLaw n) (cavityClipped_measurable i r)
      _ ≤ ∑ _i : Fin n, Real.exp 1*(Real.exp 1-1)*r := Finset.sum_le_sum (fun i _ => cavity_clipped i hr)
      _ = _ := by simp
  · intro i _
    refine ((integrable_const (μ := disorderLaw n) (1:ℝ)).indicator (cavityClipped_measurable i r)).congr (ae_of_all _ ?_)
    intro W
    by_cases hW : Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r <;> simp [hW]

lemma cavityClippedCount_tail {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) :
    (disorderLaw n).real {W | b ≤ cavityClippedCount W r} ≤ (n:ℝ)*(Real.exp 1*(Real.exp 1-1)*r)/b := by
  have ht := integral_dominates_event (μ := disorderLaw n) (E := {W | b ≤ cavityClippedCount W r}) ((cavityClippedCount_integrable r).div_const b)
    (fun W => div_nonneg (cavityClippedCount_nonneg W r) hb.le) (fun W hW => (le_div_iff₀ hb).mpr (by simpa using hW))
  rw [integral_div] at ht
  exact ht.trans (div_le_div_of_nonneg_right (cavityClippedCount_expectation hr) hb.le)

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma variance_linear_nonneg (a : Fin n → ℝ) : 0 ≤ variance W (linearObservable a) := mean_nonneg _ (fun _ => sq_nonneg _)

lemma variance_linear_norm_bound (a : Fin n → ℝ) : variance W (linearObservable a) ≤ covarianceNorm W*(∑ i, a i^2) := by
  have hh := variance_linear_le_norm W (WithLp.toLp 2 a)
  rwa [EuclideanSpace.real_norm_sq_eq] at hh

lemma linear_dirichlet_coeff_bound (A : Finset (Fin n)) (a : Fin n → ℝ) {B : ℝ} (_hB : 0 ≤ B)
    (hz : ∀ i ∈ A, cavityNormalization W i ≤ B) :
    (∑ i ∈ A, a i^2) ≤ B^2*dirichlet W (linearObservable a) := by
  have ht (i : Fin n) (hi : i ∈ A) : a i^2 ≤ B^2*(alphaSite W i*a i^2) := by
    have hZ := cavityNormalization_ge_one W i
    have hα := alphaSite_pos W i
    have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ cavityNormalization W i) (hz i hi) 2
    have hh := alphaSite_normalization W i
    have hmul := mul_le_mul_of_nonneg_left hsq hα.le
    have hn : 1 ≤ B^2*alphaSite W i := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg (a i))]
  calc
    _ ≤ ∑ i ∈ A, B^2*(alphaSite W i*a i^2) := Finset.sum_le_sum ht
    _ = B^2*(∑ i ∈ A, alphaSite W i*a i^2) := by rw [Finset.mul_sum]
    _ ≤ B^2*(∑ i : Fin n, alphaSite W i*a i^2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => mul_nonneg (alphaSite_pos W i).le (sq_nonneg _))
    _ = _ := by rw [dirichlet_linear_eq]

def restrictCoeff (A : Finset (Fin n)) (a : Fin n → ℝ) : Fin n → ℝ := fun i => if i ∈ A then a i else 0

lemma restrictCoeff_sum_sq (A : Finset (Fin n)) (a : Fin n → ℝ) :
    (∑ i : Fin n, restrictCoeff A a i^2) = ∑ i ∈ A, a i^2 := by
  simp [restrictCoeff,ite_pow,Finset.sum_ite_mem]

lemma restrictCoeff_linear (A : Finset (Fin n)) (a : Fin n → ℝ) (x : Spin n) :
    linearObservable (restrictCoeff A a) x = ∑ i ∈ A, a i*spinValue (x i) := by
  simp [linearObservable,restrictCoeff,ite_mul,Finset.sum_ite_mem]

lemma restrictCoeff_linear_sq (A : Finset (Fin n)) (a : Fin n → ℝ) (x : Spin n) :
    linearObservable (restrictCoeff A a) x^2 ≤ (A.card:ℝ)*(∑ i ∈ A, a i^2) := by
  rw [restrictCoeff_linear]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq A a (fun i => spinValue (x i))
  simp only [spinValue_sq,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  nlinarith

lemma variance_linear_split_bound (A : Finset (Fin n)) (a : Fin n → ℝ) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hzG : ∀ i ∈ A, cavityNormalization W i ≤ B)
    (hzB : ∀ i ∈ Aᶜ, cavityNormalization W i ≤ K) :
    variance W (linearObservable a) ≤
      (2*B^2*covarianceNorm W+2*(Aᶜ.card:ℝ)*K^2)*dirichlet W (linearObservable a) := by
  have hsplit (x : Spin n) : linearObservable a x = linearObservable (restrictCoeff A a) x+linearObservable (restrictCoeff Aᶜ a) x := by
    rw [restrictCoeff_linear,restrictCoeff_linear,Finset.sum_add_sum_compl]
    rfl
  have hv : variance W (linearObservable a) ≤ 2*variance W (linearObservable (restrictCoeff A a))+2*variance W (linearObservable (restrictCoeff Aᶜ a)) := by
    simp only [variance,mean_linearObservable,sub_zero]
    rw [← mean_const_mul,← mean_const_mul,← mean_add]
    apply mean_mono
    intro x
    rw [hsplit]
    nlinarith [sq_nonneg (linearObservable (restrictCoeff A a) x-linearObservable (restrictCoeff Aᶜ a) x)]
  have hG := variance_linear_norm_bound W (restrictCoeff A a)
  rw [restrictCoeff_sum_sq] at hG
  have hGB := linear_dirichlet_coeff_bound W A a hB hzG
  have hBC := linear_dirichlet_coeff_bound W Aᶜ a hK hzB
  have hVB : variance W (linearObservable (restrictCoeff Aᶜ a)) ≤ (Aᶜ.card:ℝ)*(∑ i ∈ Aᶜ, a i^2) := by
    rw [variance,mean_linearObservable]
    simp only [sub_zero]
    exact (mean_mono W (restrictCoeff_linear_sq Aᶜ a)).trans_eq (mean_const _ _)
  have hN : 0 ≤ covarianceNorm W := norm_nonneg _
  have hC : 0 ≤ (Aᶜ.card:ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hGB hN,mul_le_mul_of_nonneg_left hBC hC]

lemma linear_ratio_global_bound (a : Fin n → ℝ) (ha : a ≠ 0) :
    variance W (linearObservable a)/dirichlet W (linearObservable a) ≤
      covarianceNorm W*(∑ i : Fin n, cavityNormalization W i)^2 := by
  let B := ∑ i : Fin n, cavityNormalization W i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => by linarith [cavityNormalization_ge_one W i]
  have hZ (i : Fin n) (_ : i ∈ Finset.univ) : cavityNormalization W i ≤ B :=
    Finset.single_le_sum (fun j _ => by linarith [cavityNormalization_ge_one W j]) (Finset.mem_univ i)
  have hd := linear_dirichlet_coeff_bound W Finset.univ a hB hZ
  have hV := variance_linear_norm_bound W a
  apply (div_le_iff₀ (dirichlet_linear_pos W ha)).mpr
  have hN : 0 ≤ covarianceNorm W := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hd hN]

lemma linear_ratios_bdd : BddAbove {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧ r = variance W (linearObservable a)/dirichlet W (linearObservable a)} := by
  refine ⟨covarianceNorm W*(∑ i : Fin n, cavityNormalization W i)^2,?_⟩
  rintro r ⟨a,ha,rfl⟩
  exact linear_ratio_global_bound W a ha

lemma linear_ratios_nonempty (hn : 0 < n) : Set.Nonempty {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧ r = variance W (linearObservable a)/dirichlet W (linearObservable a)} := by
  refine ⟨_,(fun _ => 1),?_,rfl⟩
  intro hh
  have he := congrFun hh ⟨0,hn⟩
  norm_num at he

lemma linear_ratio_le (a : Fin n → ℝ) (ha : a ≠ 0) :
    variance W (linearObservable a)/dirichlet W (linearObservable a) ≤ linearRayleigh W :=
  le_csSup (linear_ratios_bdd W) ⟨a,ha,rfl⟩

lemma linearRayleigh_split_bound (hn : 0 < n) (A : Finset (Fin n)) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hzG : ∀ i ∈ A, cavityNormalization W i ≤ B)
    (hzB : ∀ i ∈ Aᶜ, cavityNormalization W i ≤ K) :
    linearRayleigh W ≤ 2*B^2*covarianceNorm W+2*(Aᶜ.card:ℝ)*K^2 := by
  apply csSup_le (linear_ratios_nonempty W hn)
  rintro r ⟨a,ha,rfl⟩
  exact (div_le_iff₀ (dirichlet_linear_pos W ha)).mpr (variance_linear_split_bound W A a hB hK hzG hzB)

lemma linearRayleigh_smallBall (a : Fin n → ℝ) (ha : ∑ i, a i^2 = 1) {b : ℝ} (hb : 0 ≤ b) :
    b^2*(1-linearSmallBall W a b) ≤ linearRayleigh W := by
  have hane : a ≠ 0 := by intro hh; simp only [hh,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero] at ha; norm_num at ha
  have hd := dirichlet_linear_le W a
  rw [ha] at hd
  have hdp := dirichlet_linear_pos W hane
  have hV := variance_linear_nonneg W a
  have hr : variance W (linearObservable a) ≤ variance W (linearObservable a)/dirichlet W (linearObservable a) :=
    (le_div_iff₀ hdp).mpr (by nlinarith)
  exact (variance_linear_smallBall W a hb).trans (hr.trans (linear_ratio_le W a hane))

end

section

open Set Filter MeasureTheory

variable {n : ℕ}

lemma variance_linear_continuous (a : Fin n → ℝ) : Continuous (fun W : Disorder n => variance W (linearObservable a)) := by
  simp_rw [variance,mean_linearObservable]
  simp only [sub_zero,mean]
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul continuous_const

lemma alphaSite_continuous (i : Fin n) : Continuous (fun W : Disorder n => alphaSite W i) := by
  unfold alphaSite mean
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul (((Real.continuous_cosh.comp (localField_continuous i x)).inv₀ (fun _ => (Real.cosh_pos _).ne')).pow 2)

lemma dirichlet_linear_continuous (a : Fin n → ℝ) : Continuous (fun W : Disorder n => dirichlet W (linearObservable a)) := by
  simp only [dirichlet_linear_eq]
  apply continuous_finsetSum
  intro i _
  exact (alphaSite_continuous i).mul continuous_const

lemma linear_ratio_continuous (a : Fin n → ℝ) (ha : a ≠ 0) :
    Continuous (fun W : Disorder n => variance W (linearObservable a)/dirichlet W (linearObservable a)) :=
  (variance_linear_continuous a).div (dirichlet_linear_continuous a) (fun W => (dirichlet_linear_pos W ha).ne')

lemma linearRayleigh_eq_iSup (W : Disorder n) : linearRayleigh W =
    ⨆ a : {a : Fin n → ℝ // a ≠ 0}, variance W (linearObservable a.val)/dirichlet W (linearObservable a.val) := by
  change sSup _ = sSup _
  congr 1
  ext r
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,ha⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a.val,a.property,rfl⟩

lemma linearRayleigh_measurable (n : ℕ) : Measurable (linearRayleigh (n := n)) := by
  have hh : LowerSemicontinuous (linearRayleigh (n := n)) := by
    change LowerSemicontinuous (fun W : Disorder n => linearRayleigh W)
    simp_rw [linearRayleigh_eq_iSup]
    apply lowerSemicontinuous_ciSup
    · intro W
      refine ⟨covarianceNorm W*(∑ i : Fin n, cavityNormalization W i)^2,?_⟩
      rintro r ⟨a,rfl⟩
      exact linear_ratio_global_bound W a.val a.property
    · intro a
      exact (linear_ratio_continuous a.val a.property).lowerSemicontinuous
  exact hh.measurable

end

open Set Filter MeasureTheory

lemma shift_rpow_neg_tendsto {p : ℝ} (hp : 0 < p) : Tendsto (fun n : ℕ => (n+4:ℝ)^(-p)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hp).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 4))
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using hh

lemma cavity_max_rate_identity {x : ℝ} (hx : 0 < x) :
    x*(2*Real.exp 20000/(x^(1/100:ℝ))^200) = (2*Real.exp 20000)*x^(-1:ℝ) := by
  rw [← Real.rpow_mul_natCast hx.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

lemma cavity_count_rate_identity {x : ℝ} (hx : 0 < x) :
    x*(Real.exp 1*(Real.exp 1-1)*x^(-1/2:ℝ))/x^(3/5:ℝ) = (Real.exp 1*(Real.exp 1-1))*x^(-1/10:ℝ) := by
  calc
    _ = (Real.exp 1*(Real.exp 1-1))*(x^((1:ℝ))*x^(-1/2:ℝ)/x^(3/5:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hx,← Real.rpow_sub hx]; congr 2; norm_num

lemma cavity_overlap_rate_identity {x : ℝ} (hx : 0 < x) :
    2*(x^(1/100:ℝ))^2*(x^(-3/5:ℝ)+x⁻¹^2)/x^(-1/2:ℝ) =
      2*(x^(-2/25:ℝ)+x^(-37/25:ℝ)) := by
  have he : x⁻¹^2 = x^(-2:ℝ) := by rw [Real.rpow_neg hx.le,Real.rpow_two,inv_pow]
  rw [he,← Real.rpow_mul_natCast hx.le]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = 2*((x^(1/100*2:ℝ)*x^(-3/5:ℝ)/x^(-1/2:ℝ))+(x^(1/100*2:ℝ)*x^(-2:ℝ)/x^(-1/2:ℝ))) := by ring_nf
    _ = _ := by rw [← Real.rpow_add hx,← Real.rpow_sub hx,← Real.rpow_add hx,← Real.rpow_sub hx]; congr 2 <;> norm_num

lemma cavity_overlap_rate_eventually : ∀ᶠ n : ℕ in atTop,
    2*((n+4:ℝ)^(1/100:ℝ))^2*((n+4:ℝ)^(-3/5:ℝ)+(n+4:ℝ)⁻¹^2) ≤ (n+4:ℝ)^(-1/2:ℝ) := by
  have hh := ((shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<2/25)).add (shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<37/25))).const_mul 2
  simp only [mul_zero,add_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  apply (div_le_one (by positivity : (0:ℝ)<(n+4:ℝ)^(-1/2:ℝ))).mp
  rw [cavity_overlap_rate_identity (by positivity)]
  simpa only [neg_div] using hn.le

lemma rayleigh_error_rate_identity {x : ℝ} (hx : 0 < x) :
    (x^(3/5:ℝ)*(x^(1/100:ℝ))^2)/x^(2/3:ℝ) = x^(-7/150:ℝ) := by
  rw [← Real.rpow_mul_natCast hx.le,← Real.rpow_add hx,← Real.rpow_sub hx]
  norm_num

lemma rayleigh_error_rate_eventually : ∀ᶠ n : ℕ in atTop,
    (n+4:ℝ)^(3/5:ℝ)*((n+4:ℝ)^(1/100:ℝ))^2 ≤ (n+4:ℝ)^(2/3:ℝ) := by
  filter_upwards [(shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<7/150)).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  apply (div_le_one (by positivity : (0:ℝ)<(n+4:ℝ)^(2/3:ℝ))).mp
  rw [rayleigh_error_rate_identity (by positivity)]
  simpa only [neg_div] using hn.le

lemma cavity_max_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | ∃ i, (n+4:ℝ)^(1/100:ℝ) ≤ cavityNormalization W i}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (g := fun n : ℕ => (2*Real.exp 20000)*(n+4:ℝ)^(-1:ℝ))
  · intro n
    have hh := all_cavity_tail (n := n+4) (by positivity : (0:ℝ)<(n+4:ℝ)^(1/100:ℝ)) 200
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
    rwa [cavity_max_rate_identity (by positivity)] at hh
  · simpa using (shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<1)).const_mul (2*Real.exp 20000)

lemma cavity_count_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | (n+4:ℝ)^(3/5:ℝ) ≤ cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ))}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (g := fun n : ℕ => (Real.exp 1*(Real.exp 1-1))*(n+4:ℝ)^(-1/10:ℝ))
  · intro n
    have hh := cavityClippedCount_tail (n := n+4) (by positivity : (0:ℝ)≤(n+4:ℝ)^(-1/2:ℝ)) (by positivity : (0:ℝ)<(n+4:ℝ)^(3/5:ℝ))
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
    simp only [← neg_div] at hh
    rwa [cavity_count_rate_identity (by positivity)] at hh
  · simpa only [mul_zero,neg_div] using (shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<1/10)).const_mul (Real.exp 1*(Real.exp 1-1))

lemma cavity_overlap_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro a ha
    obtain ⟨C,_hC,hp⟩ := natural_GibbsOverlap_tight ha
    have ht : Tendsto (fun n : ℕ => (n+4:ℝ)^(1/15:ℝ)) atTop atTop := by
      have hh := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/15)).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 4))
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using hh
    filter_upwards [hp,tendsto_atTop.mp ht C] with n hn hCn
    refine lt_of_le_of_lt (measureReal_mono ?_) hn
    intro W hW
    change C/(n+4:ℝ)^(2/3:ℝ) ≤ gibbsOverlap W
    change (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W at hW
    apply le_trans _ hW
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+4:ℝ)^(2/3:ℝ))).mpr
    rw [← Real.rpow_add (by positivity : (0:ℝ)<n+4)]
    norm_num
    exact hCn

lemma rayleigh_cavity_good_bound (n : ℕ) (W : Disorder (n+4))
    (hrate : 2*((n+4:ℝ)^(1/100:ℝ))^2*((n+4:ℝ)^(-3/5:ℝ)+(n+4:ℝ)⁻¹^2) ≤ (n+4:ℝ)^(-1/2:ℝ))
    (herr : (n+4:ℝ)^(3/5:ℝ)*((n+4:ℝ)^(1/100:ℝ))^2 ≤ (n+4:ℝ)^(2/3:ℝ))
    (hZ : ∀ i, cavityNormalization W i < (n+4:ℝ)^(1/100:ℝ))
    (hQ : gibbsOverlap W < (n+4:ℝ)^(-3/5:ℝ))
    (hC : cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ)) < (n+4:ℝ)^(3/5:ℝ)) :
    linearRayleigh W ≤ 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) := by
  classical
  have hR (i : Fin (n+4)) : cavityOverlap W i ≤ (n+4:ℝ)^(-1/2:ℝ) := by
    have hh := cavityOverlap_compare W i
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
    refine hh.trans (le_trans ?_ hrate)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [cavityNormalization_ge_one W i]) (hZ i).le 2) (by norm_num)
    · exact add_le_add hQ.le le_rfl
    · exact add_nonneg (gibbsOverlap_nonneg W) (sq_nonneg _)
    · positivity
  let A : Finset (Fin (n+4)) := Finset.univ.filter (fun i => cavityNormalization W i ≤ Real.exp 1+1)
  have hcard : (Aᶜ.card:ℝ) = cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ)) := by
    rw [cavityClippedCount]
    have he (i : Fin (n+4)) : i ∈ Aᶜ ↔ Real.exp 1+1 < cavityNormalization W i := by simp [A]
    calc
      _ = ∑ i : Fin (n+4), if i ∈ Aᶜ then (1:ℝ) else 0 := by rw [← Finset.sum_filter]; simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [he,hR i,and_true]
  have hb := linearRayleigh_split_bound W (by omega : 0<n+4) A
    (by positivity : (0:ℝ)≤Real.exp 1+1) (by positivity : (0:ℝ)≤(n+4:ℝ)^(1/100:ℝ))
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun i _ => (hZ i).le)
  rw [hcard] at hb
  have hm := mul_le_mul_of_nonneg_right hC.le (sq_nonneg ((n+4:ℝ)^(1/100:ℝ)))
  linarith

lemma linearRayleigh_cavity_comparison : ∀ α : ℝ, 0 < α → ∀ᶠ n : ℕ in atTop,
    (disorderLaw (n+4)).real {W | 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W} < α := by
  intro α hα
  filter_upwards [cavity_overlap_rate_eventually,rayleigh_error_rate_eventually,
    cavity_max_tail_zero.eventually (gt_mem_nhds (show 0<α/3 by positivity)),
    cavity_overlap_tail_zero.eventually (gt_mem_nhds (show 0<α/3 by positivity)),
    cavity_count_tail_zero.eventually (gt_mem_nhds (show 0<α/3 by positivity))] with n hr he hZ hQ hC
  have hs : {W : Disorder (n+4) | 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W} ⊆
      ({W | ∃ i, (n+4:ℝ)^(1/100:ℝ) ≤ cavityNormalization W i} ∪ {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}) ∪
      {W | (n+4:ℝ)^(3/5:ℝ) ≤ cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ))} := by
    intro W hW
    by_contra hh
    simp only [mem_union,mem_ofPred_eq,not_or,not_exists,not_le] at hh
    exact (not_lt_of_ge (rayleigh_cavity_good_bound n W hr he hh.1.1 hh.1.2 hh.2)) hW
  have hp := (measureReal_mono (μ := disorderLaw (n+4)) hs).trans (measureReal_union_le _ _)
  have hp' := measureReal_union_le (μ := disorderLaw (n+4))
    {W | ∃ i, (n+4:ℝ)^(1/100:ℝ) ≤ cavityNormalization W i} {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}
  linarith

lemma linearRayleigh_lower_tight {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | linearRayleigh W ≤ c*(n+4:ℝ)^(2/3:ℝ)} < α := by
  obtain ⟨b,hb,hp⟩ := natural_smallBall_tight (by norm_num : (0:ℝ) < 1/2) hα
  refine ⟨b^2/2,by positivity,?_⟩
  filter_upwards [hp] with n hn
  refine lt_of_le_of_lt (measureReal_mono ?_) hn
  intro W hW u hu
  have husq : ∑ i, u i^2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq u,hu,one_pow]
  have hV := linearRayleigh_smallBall W (fun i => u i) husq (show 0 ≤ b*(n+4:ℝ)^(1/3:ℝ) by positivity)
  rw [mul_pow,third_power_square (by positivity : (0:ℝ) ≤ n+4)] at hV
  change linearRayleigh W ≤ b^2/2*(n+4:ℝ)^(2/3:ℝ) at hW
  have hP : 0 < b^2*(n+4:ℝ)^(2/3:ℝ) := by positivity
  nlinarith

lemma linearRayleigh_upper_tight {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | C*(n+4:ℝ)^(2/3:ℝ) ≤ linearRayleigh W} < α := by
  obtain ⟨K,hK,hp⟩ := covariance_upper_tight (show 0<α/2 by positivity)
  let C := 2*(Real.exp 1+1)^2*K+3
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hp,linearRayleigh_cavity_comparison (α/2) (by positivity)] with n hn hc
  have hs : {W : Disorder (n+4) | C*(n+4:ℝ)^(2/3:ℝ) ≤ linearRayleigh W} ⊆
      {W | K*(n+4:ℝ)^(2/3:ℝ) ≤ covarianceNorm W} ∪
      {W | 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W} := by
    intro W hW
    by_cases hh : K*(n+4:ℝ)^(2/3:ℝ) ≤ covarianceNorm W
    · exact Or.inl hh
    · right
      change C*(n+4:ℝ)^(2/3:ℝ) ≤ linearRayleigh W at hW
      have hN := lt_of_not_ge hh
      have hmul := mul_lt_mul_of_pos_left hN (show 0<2*(Real.exp 1+1)^2 by positivity)
      dsimp only [C] at hW
      have hpN : 0<(n+4:ℝ)^(2/3:ℝ) := by positivity
      change 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W
      nlinarith
  have hb := (measureReal_mono (μ := disorderLaw (n+4)) hs).trans (measureReal_union_le _ _)
  linarith

theorem linearRayleigh_natural_scale (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (disorderLaw n).real {W |
      (n:ℝ)^(2/3:ℝ)/M n ≤ linearRayleigh W ∧ linearRayleigh W ≤ M n*(n:ℝ)^(2/3:ℝ)}) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  have hh := tight_interval_limit (fun n => disorderLaw (n+4)) (fun _ W => linearRayleigh W)
    (fun n => linearRayleigh_measurable (n+4))
    (fun n => (n+4:ℝ)^(2/3:ℝ)) (fun _ => by positivity)
    (fun _ hα => linearRayleigh_lower_tight hα) (fun _ hα => linearRayleigh_upper_tight hα)
    (fun n => M (n+4)) (fun n => hMpos (n+4)) (hM.comp (tendsto_add_atTop_nat 4))
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

lemma probability_intersection_tendsto_one {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Set (X n)) (_hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hpA : Tendsto (fun n => (μ n).real (A n)) atTop (𝓝 1))
    (hpB : Tendsto (fun n => (μ n).real (B n)) atTop (𝓝 1)) :
    Tendsto (fun n => (μ n).real (A n ∩ B n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => (μ n).real (A n)+(μ n).real (B n)-1) (h := fun _ => (1:ℝ))
  · simpa using (hpA.add hpB).sub_const 1
  · exact tendsto_const_nhds
  · intro n
    have hadd := measureReal_union_add_inter (μ := μ n) (s := A n) (hB n)
    have hle : (μ n).real (A n ∪ B n) ≤ 1 := measureReal_le_one
    linarith
  · exact fun _ => measureReal_le_one

theorem covariance_and_linear_tests (M : ℕ → ℝ)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ covarianceNorm W ∧
      covarianceNorm W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ linearRayleigh W ∧
      linearRayleigh W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3)}).toReal) atTop (𝓝 1) := by
  have hh := probability_intersection_tendsto_one disorderLaw
    (fun n => {W | (n:ℝ)^(2/3:ℝ)/M n ≤ covarianceNorm W ∧ covarianceNorm W ≤ M n*(n:ℝ)^(2/3:ℝ)})
    (fun n => {W | (n:ℝ)^(2/3:ℝ)/M n ≤ linearRayleigh W ∧ linearRayleigh W ≤ M n*(n:ℝ)^(2/3:ℝ)})
    (fun n => (measurableSet_le measurable_const (covarianceNorm_continuous n).measurable).inter (measurableSet_le (covarianceNorm_continuous n).measurable measurable_const))
    (fun n => (measurableSet_le measurable_const (linearRayleigh_measurable n)).inter (measurableSet_le (linearRayleigh_measurable n) measurable_const))
    (covariance_natural_scale M hMpos hM) (linearRayleigh_natural_scale M hMpos hM)
  simpa only [Set.inter_def,Set.mem_ofPred_eq,and_assoc,Measure.real] using hh

end CriticalSK

end

end OAI
