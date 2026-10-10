import Mathlib
import OAI.Analysis.Conductivity.Fourier.SpectralTrace
import OAI.Analysis.Conductivity.Fourier.CylinderFourier

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

abbrev EndAxisMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev EndAxisL2 := Lp ℂ 2 EndAxisMeasure

lemma complexLp_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

def axialRateField (m : ℝ) (a : ℂ) (t : ℝ) : ℂ :=
  (m*Real.exp (-m*t):ℝ)*a

lemma axialRateField_continuous (m : ℝ) (a : ℂ) :
    Continuous (axialRateField m a) := by unfold axialRateField; fun_prop

lemma axialRateField_norm_sq (m : ℝ) (a : ℂ) (t : ℝ) :
    ‖axialRateField m a t‖^2=(2*m^2*Real.exp (-2*m*t)*‖a‖^2)/2 := by
  unfold axialRateField
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,
    ←Real.exp_nat_mul]
  ring_nf

lemma axialRateField_memLp {m : ℝ} (hm : 0 ≤ m) (a : ℂ) :
    MemLp (axialRateField m a) 2 EndAxisMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (axialRateField_continuous m a).aestronglyMeasurable).mpr
  simpa only [axialRateField_norm_sq] using ((poisson_mode_energy hm a).1.div_const 2)

def axialRateLp (m : ℝ) (hm : 0 ≤ m) (a : ℂ) : EndAxisL2 :=
  (axialRateField_memLp hm a).toLp _

lemma axialRateLp_ae (m : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    axialRateLp m hm a =ᵐ[EndAxisMeasure] axialRateField m a :=
  (axialRateField_memLp hm a).coeFn_toLp

lemma axialRateLp_norm_sq (m : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    ‖axialRateLp m hm a‖^2=(m*‖a‖^2)/2 := by
  rw [complexLp_norm_sq]
  calc
    (∫ t,‖axialRateLp m hm a t‖^2 ∂EndAxisMeasure)=
        ∫ t,‖axialRateField m a t‖^2 ∂EndAxisMeasure :=
      by
        apply integral_congr_ae
        filter_upwards [axialRateLp_ae m hm a] with t ht
        rw [ht]
    _=(∫ t in Ioi (0:ℝ),2*m^2*Real.exp (-2*m*t)*‖a‖^2)/2 := by
      simp only [axialRateField_norm_sq,integral_div,EndAxisMeasure]
    _=(m*‖a‖^2)/2 := by rw [(poisson_mode_energy hm a).2]

lemma axialRateLp_add (m : ℝ) (hm : 0 ≤ m) (a b : ℂ) :
    axialRateLp m hm (a+b)=axialRateLp m hm a+axialRateLp m hm b := by
  apply Lp.ext
  filter_upwards [axialRateLp_ae m hm (a+b),axialRateLp_ae m hm a,axialRateLp_ae m hm b,
    Lp.coeFn_add (axialRateLp m hm a) (axialRateLp m hm b)] with t h h1 h2 h3
  rw [h,h3]
  simp only [Pi.add_apply]
  rw [h1,h2]
  exact mul_add _ _ _

lemma axialRateLp_smul (m : ℝ) (hm : 0 ≤ m) (c a : ℂ) :
    axialRateLp m hm (c*a)=c•axialRateLp m hm a := by
  apply Lp.ext
  filter_upwards [axialRateLp_ae m hm (c*a),axialRateLp_ae m hm a,
    Lp.coeFn_smul c (axialRateLp m hm a)] with t h h1 h2
  rw [h,h2]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h1]
  unfold axialRateField
  ring

lemma axialRateLp_zero (m : ℝ) (hm : 0 ≤ m) : axialRateLp m hm 0=0 := by
  apply norm_eq_zero.mp
  have he := axialRateLp_norm_sq m hm 0
  simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div] at he
  nlinarith only [he,norm_nonneg (axialRateLp m hm 0)]

def axialRateSequence {ι : Type*} (m : ι → ℝ) (hm : ∀ i,0 ≤ m i)
    (a : ι → ℂ) (ha : Summable (fun i => m i*‖a i‖^2)) :
    lp (fun _ : ι => EndAxisL2) 2 :=
  ⟨fun i => axialRateLp (m i) (hm i) (a i),by
    apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,axialRateLp_norm_sq] using ha.div_const 2⟩

def cylinderRateField (m : TorusModes → ℝ) (hm : ∀ i,0 ≤ m i)
    (a : TorusModes → ℂ) (ha : Summable (fun i => m i*‖a i‖^2)) :
    CylinderL2 EndAxisMeasure :=
  cylinderFourier EndAxisMeasure (axialRateSequence m hm a ha)

lemma cylinderRateField_norm_sq (m : TorusModes → ℝ) (hm : ∀ i,0 ≤ m i)
    (a : TorusModes → ℂ) (ha : Summable (fun i => m i*‖a i‖^2)) :
    ‖cylinderRateField m hm a ha‖^2=(∑' i,m i*‖a i‖^2)/2 := by
  unfold cylinderRateField
  rw [cylinderFourier_norm_sq]
  change (∑' i,‖axialRateLp (m i) (hm i) (a i)‖^2)=_
  simp only [axialRateLp_norm_sq,tsum_div_const]

lemma cylinderRateField_hasSum (m : TorusModes → ℝ) (hm : ∀ i,0 ≤ m i)
    (a : TorusModes → ℂ) (ha : Summable (fun i => m i*‖a i‖^2)) :
    HasSum (fun i => cylinderMode EndAxisMeasure i (axialRateLp (m i) (hm i) (a i)))
      (cylinderRateField m hm a ha) :=
  cylinderFourier_hasSum EndAxisMeasure (axialRateSequence m hm a ha)

abbrev FiniteAxisMeasure (R : ℝ) : Measure ℝ := volume.restrict (Ioc 0 R)
abbrev FiniteAxisL2 (R : ℝ) := Lp ℂ 2 (FiniteAxisMeasure R)

def axialDecayField (m : ℝ) (a : ℂ) (t : ℝ) : ℂ := (Real.exp (-m*t):ℂ)*a

lemma axialDecayField_continuous (m : ℝ) (a : ℂ) :
    Continuous (axialDecayField m a) := by unfold axialDecayField; fun_prop

lemma axialDecayField_memLp (m R : ℝ) (a : ℂ) :
    MemLp (axialDecayField m a) 2 (FiniteAxisMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm (axialDecayField_continuous m a).aestronglyMeasurable).mpr
  exact (((axialDecayField_continuous m a).norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self

def finiteDecayLp (m R : ℝ) (a : ℂ) : FiniteAxisL2 R :=
  (axialDecayField_memLp m R a).toLp _

lemma finiteDecayLp_ae (m R : ℝ) (a : ℂ) :
    finiteDecayLp m R a =ᵐ[FiniteAxisMeasure R] axialDecayField m a :=
  (axialDecayField_memLp m R a).coeFn_toLp

lemma finiteDecayLp_norm_sq {m R : ℝ} (hm : 0 ≤ m) (hR : 0≤R) (a : ℂ) :
    ‖finiteDecayLp m R a‖^2≤R*‖a‖^2 := by
  rw [complexLp_norm_sq]
  have he : (∫ t,‖finiteDecayLp m R a t‖^2 ∂FiniteAxisMeasure R)=
      ∫ t in Ioc (0:ℝ) R,‖axialDecayField m a t‖^2 := by
    apply integral_congr_ae
    filter_upwards [finiteDecayLp_ae m R a] with t ht
    rw [ht]
  rw [he]
  calc
    (∫ t in Ioc (0:ℝ) R,‖axialDecayField m a t‖^2) ≤
        ∫ t in Ioc (0:ℝ) R,‖a‖^2 := by
      apply setIntegral_mono_on
        ((axialDecayField_memLp m R a).integrable_norm_pow (by decide : (2:ℕ)≠0))
        (integrable_const _) measurableSet_Ioc
      intro t ht
      have hb : Real.exp (-m*t)≤1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) ht.1.le)
      have hn : ‖axialDecayField m a t‖≤‖a‖ := by
        unfold axialDecayField
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_right hb (norm_nonneg a)).trans_eq (one_mul _)
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    _=R*‖a‖^2 := by
      rw [integral_const]
      change ((volume.restrict (Ioc (0:ℝ) R)) univ).toReal * ‖a‖^2=_
      rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,
        sub_zero,ENNReal.toReal_ofReal hR]

lemma finiteDecayLp_add (m R : ℝ) (a b : ℂ) :
    finiteDecayLp m R (a+b)=finiteDecayLp m R a+finiteDecayLp m R b := by
  apply Lp.ext
  filter_upwards [finiteDecayLp_ae m R (a+b),finiteDecayLp_ae m R a,finiteDecayLp_ae m R b,
    Lp.coeFn_add (finiteDecayLp m R a) (finiteDecayLp m R b)] with t h h1 h2 h3
  rw [h,h3]
  simp only [Pi.add_apply]
  rw [h1,h2]
  exact mul_add _ _ _

lemma finiteDecayLp_smul (m R : ℝ) (c a : ℂ) :
    finiteDecayLp m R (c*a)=c•finiteDecayLp m R a := by
  apply Lp.ext
  filter_upwards [finiteDecayLp_ae m R (c*a),finiteDecayLp_ae m R a,
    Lp.coeFn_smul c (finiteDecayLp m R a)] with t h h1 h2
  rw [h,h2]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h1]
  unfold axialDecayField
  ring

lemma finiteDecayLp_zero (m R : ℝ) : finiteDecayLp m R 0=0 := by
  simpa only [zero_mul,zero_smul] using finiteDecayLp_smul m R 0 0

lemma finiteAxisMeasure_le (R : ℝ) : FiniteAxisMeasure R≤EndAxisMeasure :=
  Measure.restrict_mono (fun _ h => h.1) le_rfl

def endAxisRestrict (R : ℝ) : EndAxisL2 →L[ℝ] FiniteAxisL2 R :=
  Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp) (by simpa only [one_smul] using finiteAxisMeasure_le R)

lemma endAxisRestrict_ae (R : ℝ) (f : EndAxisL2) :
    endAxisRestrict R f =ᵐ[FiniteAxisMeasure R] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp)
    (by simpa only [one_smul] using finiteAxisMeasure_le R) f

lemma endAxisRestrict_norm (R : ℝ) (f : EndAxisL2) : ‖endAxisRestrict R f‖≤‖f‖ := by
  have hn : ‖endAxisRestrict R‖≤1 := by
    simpa only [endAxisRestrict,ENNReal.toReal_one,Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E:=ℂ) (p:=2) (c:=1) (by simp)
        (by simpa only [one_smul] using finiteAxisMeasure_le R)
  exact ((endAxisRestrict R).le_opNorm f).trans
    ((mul_le_mul_of_nonneg_right hn (norm_nonneg f)).trans_eq (one_mul _))

lemma finiteDecayLp_rate (m R : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    finiteDecayLp m R ((m:ℂ)*a)=endAxisRestrict R (axialRateLp m hm a) := by
  apply Lp.ext
  filter_upwards [finiteDecayLp_ae m R ((m:ℂ)*a),
    endAxisRestrict_ae R (axialRateLp m hm a),
    (Measure.absolutelyContinuous_of_le (finiteAxisMeasure_le R)).ae_eq (axialRateLp_ae m hm a)]
    with t h h1 h2
  rw [h,h1,h2]
  simp only [axialDecayField,axialRateField,Complex.ofReal_mul]
  ring

lemma finiteDecayLp_rate_norm_sq (m R : ℝ) (hm : 0 ≤ m) (a : ℂ) :
    ‖finiteDecayLp m R ((m:ℂ)*a)‖^2≤(m*‖a‖^2)/2 := by
  rw [finiteDecayLp_rate m R hm a,←axialRateLp_norm_sq m hm a]
  exact pow_le_pow_left₀ (norm_nonneg _) (endAxisRestrict_norm R _) 2

def finiteDecaySequence {ι : Type*} (m : ι → ℝ) (hm : ∀ i,0 ≤ m i)
    (R : ℝ) (hR : 0≤R) (a : SpectralL2 ι) : lp (fun _ : ι => FiniteAxisL2 R) 2 :=
  ⟨fun i => finiteDecayLp (m i) R (a i),by
    apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have ha := (lp.memℓp a).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at ha
    exact (ha.mul_left R).of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => finiteDecayLp_norm_sq (hm i) hR (a i))⟩

end ScalarConductivity

end

end OAI
