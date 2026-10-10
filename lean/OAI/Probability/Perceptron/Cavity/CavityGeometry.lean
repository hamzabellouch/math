import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityCovarianceComparison
import OAI.Probability.Perceptron.Cavity.CavityPerturbationCovariance
import OAI.Probability.Perceptron.Variational.GaussianBlock

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def gaussianBlockJoin (N L : ℕ) (p : Spin N×Spin L) : Spin (N+L) :=
  WithLp.toLp 2 (Fin.addCases (fun i=>p.1 i) (fun j=>p.2 j))

lemma gaussianBlockJoin_measurable (N L : ℕ) : Measurable (gaussianBlockJoin N L) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> fun_prop

lemma gaussianBlockSplit_join (N L : ℕ) (p : Spin N×Spin L) :
    gaussianBlockSplit N L (gaussianBlockJoin N L p)=p := by
  apply Prod.ext <;> ext i <;> simp [gaussianBlockSplit,gaussianBlockJoin]

lemma gaussianBlockJoin_split (N L : ℕ) (x : Spin (N+L)) :
    gaussianBlockJoin N L (gaussianBlockSplit N L x)=x := by
  ext i
  induction i using Fin.addCases <;> simp [gaussianBlockSplit,gaussianBlockJoin]

lemma gaussianBlockJoin_norm_sq (N L : ℕ) (p : Spin N×Spin L) :
    ‖gaussianBlockJoin N L p‖^2=‖p.1‖^2+‖p.2‖^2 := by
  simpa only [gaussianBlockSplit_join] using gaussianBlockSplit_norm_sq N L (gaussianBlockJoin N L p)

lemma gaussianBlockJoin_inner (N L : ℕ) (p q : Spin N×Spin L) :
    inner ℝ (gaussianBlockJoin N L p) (gaussianBlockJoin N L q)=
      inner ℝ p.1 q.1+inner ℝ p.2 q.2 := by
  change (∑ i : Fin (N+L),gaussianBlockJoin N L q i*gaussianBlockJoin N L p i)=_
  rw [Fin.sum_univ_add]
  simp only [gaussianBlockJoin,PiLp.toLp_apply,Fin.addCases_left,Fin.addCases_right]
  rfl

def cavityRho (N L : ℕ) (z : Spin L) : ℝ := Real.sqrt (1-‖z‖^2/(N+L:ℕ))

def cavityNormalizedVec (N L : ℕ) (x : NormalizedSpin N) (z : Spin L) : Spin (N+L) :=
  gaussianBlockJoin N L (cavityRho N L z •x.val,(Real.sqrt (N+L:ℕ))⁻¹ •z)

lemma cavityRho_bounds (N L : ℕ) (z : Spin L) (hD : 0<(N+L:ℕ))
    (hz : ‖z‖^2≤(N+L:ℕ)) :
    0≤cavityRho N L z ∧ cavityRho N L z≤1 ∧
      1-cavityRho N L z≤‖z‖^2/(N+L:ℕ) := by
  have hDp : (0:ℝ)<(N+L:ℕ) := by exact_mod_cast hD
  have hq : 0≤‖z‖^2/(N+L:ℕ) := by positivity
  have hq1 : ‖z‖^2/(N+L:ℕ)≤1 := (div_le_one hDp).mpr hz
  have hsq := Real.sq_sqrt (show 0≤1-‖z‖^2/(N+L:ℕ) by linarith)
  have hp := Real.sqrt_nonneg (1-‖z‖^2/(N+L:ℕ))
  have hu : Real.sqrt (1-‖z‖^2/(N+L:ℕ))≤1 := by nlinarith
  refine ⟨hp,hu,?_⟩
  dsimp [cavityRho]
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hu)]

lemma cavityNormalizedVec_norm (N L : ℕ) (x : NormalizedSpin N) (z : Spin L)
    (hD : 0<(N+L:ℕ)) (hz : ‖z‖^2≤(N+L:ℕ)) :
    ‖cavityNormalizedVec N L x z‖=1 := by
  have hDp : (0:ℝ)<(N+L:ℕ) := by exact_mod_cast hD
  have hx : ‖x.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.prop
  have hr : 0≤1-‖z‖^2/(N+L:ℕ) := sub_nonneg.mpr ((div_le_one hDp).mpr hz)
  have hsq : ‖cavityNormalizedVec N L x z‖^2=1 := by
    rw [cavityNormalizedVec,gaussianBlockJoin_norm_sq]
    simp only [norm_smul,Real.norm_eq_abs,hx,mul_one,mul_pow,sq_abs,cavityRho,
      Real.sq_sqrt hr,inv_pow,Real.sq_sqrt hDp.le]
    rw [←div_eq_inv_mul]
    ring
  nlinarith [norm_nonneg (cavityNormalizedVec N L x z)]

lemma cavityNormalizedVec_inner (N L : ℕ) (x x' : NormalizedSpin N) (z z' : Spin L)
    (hD : 0<(N+L:ℕ)) :
    inner ℝ (cavityNormalizedVec N L x z) (cavityNormalizedVec N L x' z')=
      cavityRho N L z*cavityRho N L z'*spinOverlap x x'+inner ℝ z z'/(N+L:ℕ) := by
  have hDp : (0:ℝ)<(N+L:ℕ) := by exact_mod_cast hD
  simp only [cavityNormalizedVec,gaussianBlockJoin_inner,inner_smul_left,inner_smul_right,
    conj_trivial,spinOverlap]
  rw [show (Real.sqrt (N+L:ℕ))⁻¹*((Real.sqrt (N+L:ℕ))⁻¹*inner ℝ z z')=
      inner ℝ z z'/(N+L:ℕ) by
    rw [←mul_assoc,←pow_two,inv_pow,Real.sq_sqrt hDp.le,div_eq_mul_inv,mul_comm]]
  ring

lemma cavityNormalizedVec_overlap_error (n L : ℕ) (x x' : NormalizedSpin (n+1))
    (z z' : Spin L) {D : ℝ} (hz : ‖z‖^2≤D) (hz' : ‖z'‖^2≤D)
    (hD : D≤(n+1+L:ℕ)) :
    |inner ℝ (cavityNormalizedVec (n+1) L x z) (cavityNormalizedVec (n+1) L x' z')-
      spinOverlap x x'|≤3*D/(n+1:ℕ) := by
  have hp : 0<(n+1+L:ℕ) := by omega
  have hpr : (0:ℝ)<(n+1+L:ℕ) := by positivity
  have hD0 : 0≤D := (sq_nonneg ‖z‖).trans hz
  have hr := cavityRho_bounds (n+1) L z hp (hz.trans hD)
  have hr' := cavityRho_bounds (n+1) L z' hp (hz'.trans hD)
  have hrlo : 0≤cavityRho (n+1) L z*cavityRho (n+1) L z' := mul_nonneg hr.1 hr'.1
  have hrhi : cavityRho (n+1) L z*cavityRho (n+1) L z'≤1 := by nlinarith
  have hrerr : |cavityRho (n+1) L z*cavityRho (n+1) L z'-1|≤2*D/(n+1+L:ℕ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hrhi)]
    have ha := (hr.2.2.trans (div_le_div_of_nonneg_right hz hpr.le))
    have hb := (hr'.2.2.trans (div_le_div_of_nonneg_right hz' hpr.le))
    rw [mul_div_assoc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2.1) (sub_nonneg.mpr hr'.2.1)]
  have hi : |inner ℝ z z'|≤D := by
    apply (abs_real_inner_le_norm z z').trans
    nlinarith [sq_nonneg (‖z‖-‖z'‖)]
  rw [cavityNormalizedVec_inner _ _ _ _ _ _ hp]
  have he : cavityRho (n+1) L z*cavityRho (n+1) L z'*spinOverlap x x'+inner ℝ z z'/(n+1+L:ℕ)-spinOverlap x x'=
      (cavityRho (n+1) L z*cavityRho (n+1) L z'-1)*spinOverlap x x'+inner ℝ z z'/(n+1+L:ℕ) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_div,abs_of_pos hpr]
  have hspin : |spinOverlap x x'|≤1 := spinOverlap_abs_le x x'
  calc
    _≤2*D/(n+1+L:ℕ)*1+D/(n+1+L:ℕ) :=
      add_le_add (mul_le_mul hrerr hspin (abs_nonneg _) (by positivity))
        (div_le_div_of_nonneg_right hi hpr.le)
    _=3*D/(n+1+L:ℕ) := by ring
    _≤3*D/(n+1:ℕ) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_cast; omega)

lemma cavityNormalizedVec_covariance (n L : ℕ) (v : ℕ→ℝ) (C : ℝ) (hC : 0≤C)
    (hv : ∀ j,|v (j+1)|≤C) (x x' : NormalizedSpin (n+1)) (z z' : Spin L)
    (hz : ‖z‖^2≤(L:ℝ)+1) (hz' : ‖z'‖^2≤(L:ℝ)+1) :
    |inner ℝ (ambientBulkFeature (n+1+L) v (cavityNormalizedVec (n+1) L x z))
        (ambientBulkFeature (n+1+L) v (cavityNormalizedVec (n+1) L x' z'))-
      inner ℝ (bulkFeature (n+1) v x) (bulkFeature (n+1) v x')|≤
      cavityBulkCovarianceError n L C (3*((L:ℝ)+1)) := by
  have hD : (L:ℝ)+1≤(n+1+L:ℕ) := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0<(n+1+L:ℕ) := by omega
  let u : NormalizedSpin (n+1+L):=⟨cavityNormalizedVec (n+1) L x z,by
    simpa only [Metric.mem_sphere,dist_zero_right] using cavityNormalizedVec_norm _ _ x z hp (hz.trans hD)⟩
  let u' : NormalizedSpin (n+1+L):=⟨cavityNormalizedVec (n+1) L x' z',by
    simpa only [Metric.mem_sphere,dist_zero_right] using cavityNormalizedVec_norm _ _ x' z' hp (hz'.trans hD)⟩
  change |inner ℝ (ambientBulkFeature _ v u.val) (ambientBulkFeature _ v u'.val)-_|≤_
  rw [ambientBulkFeature_eq,ambientBulkFeature_eq,bulkFeature_inner,bulkFeature_inner]
  apply cavity_bulk_covariance_shell n L v hC (by positivity) hv (spinOverlap_abs_le x x') (spinOverlap_abs_le u u')
  exact cavityNormalizedVec_overlap_error n L x x' z z' hz hz' hD

section Sum
variable {I J : Type} [Fintype I] [Fintype J]
def gaussianSumSplit (x : EuclideanSpace ℝ (I⊕J)) : EuclideanSpace ℝ I×EuclideanSpace ℝ J :=
  (WithLp.toLp 2 (fun i=>x (.inl i)),WithLp.toLp 2 (fun j=>x (.inr j)))
def gaussianInl (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ (I⊕J) :=
  WithLp.toLp 2 (Sum.elim (fun i=>x i) (fun _=>0))
def gaussianInr (x : EuclideanSpace ℝ J) : EuclideanSpace ℝ (I⊕J) :=
  WithLp.toLp 2 (Sum.elim (fun _=>0) (fun j=>x j))
omit [Fintype I] [Fintype J] in
lemma gaussianSumSplit_measurable : Measurable (gaussianSumSplit (I:=I) (J:=J)) := by
  unfold gaussianSumSplit
  fun_prop
lemma gaussianInl_measurable : Measurable (gaussianInl (I:=I) (J:=J)) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop
lemma gaussianInr_measurable : Measurable (gaussianInr (I:=I) (J:=J)) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop
lemma gaussianSumSplit_preserving :
    MeasurePreserving (gaussianSumSplit (I:=I) (J:=J)) (stdGaussian (EuclideanSpace ℝ (I⊕J)))
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) := by
  have hI : MeasurePreserving (WithLp.toLp 2 : (I→ℝ)→EuclideanSpace ℝ I)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ I)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hJ : MeasurePreserving (WithLp.toLp 2 : (J→ℝ)→EuclideanSpace ℝ J)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ J)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  refine ⟨gaussianSumSplit_measurable,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map gaussianSumSplit_measurable (PiLp.continuous_toLp 2 _).measurable]
  convert ((hI.prod hJ).comp (measurePreserving_sumPiEquivProdPi (fun _ : I⊕J=>gaussianReal 0 1))).map_eq using 1
  rfl
lemma gaussianInl_inner (x y : EuclideanSpace ℝ I) :
    inner ℝ (gaussianInl (J:=J) x) (gaussianInl y)=inner ℝ x y := by
  change (∑ i, gaussianInl (J:=J) y i*gaussianInl x i)=_
  simp only [Fintype.sum_sum_type,gaussianInl,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,add_zero]
  rfl
lemma gaussianInr_inner (x y : EuclideanSpace ℝ J) :
    inner ℝ (gaussianInr (I:=I) x) (gaussianInr y)=inner ℝ x y := by
  change (∑ i, gaussianInr (I:=I) y i*gaussianInr x i)=_
  simp only [Fintype.sum_sum_type,gaussianInr,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,zero_add]
  rfl
lemma gaussianInl_Inr_inner (x : EuclideanSpace ℝ I) (y : EuclideanSpace ℝ J) :
    inner ℝ (gaussianInl x) (gaussianInr y)=0 := by
  change (∑ i, gaussianInr (I:=I) y i*gaussianInl x i)=_
  simp [Fintype.sum_sum_type,gaussianInl,gaussianInr]
lemma gaussianInl_norm (x : EuclideanSpace ℝ I) : ‖gaussianInl (J:=J) x‖=‖x‖ := by
  have h:=gaussianInl_inner (J:=J) x x
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x,norm_nonneg (gaussianInl (J:=J) x)]
lemma gaussianInr_norm (x : EuclideanSpace ℝ J) : ‖gaussianInr (I:=I) x‖=‖x‖ := by
  have h:=gaussianInr_inner (I:=I) x x
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x,norm_nonneg (gaussianInr (I:=I) x)]
lemma gaussianInl_linear (x : EuclideanSpace ℝ I) (g : EuclideanSpace ℝ (I⊕J)) :
    inner ℝ (gaussianInl x) g=inner ℝ x (gaussianSumSplit g).1 := by
  change (∑ i,g i*gaussianInl x i)=_
  simp only [Fintype.sum_sum_type,gaussianInl,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,add_zero]
  rfl
lemma gaussianInr_linear (x : EuclideanSpace ℝ J) (g : EuclideanSpace ℝ (I⊕J)) :
    inner ℝ (gaussianInr x) g=inner ℝ x (gaussianSumSplit g).2 := by
  change (∑ i,g i*gaussianInr x i)=_
  simp only [Fintype.sum_sum_type,gaussianInr,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,zero_add]
  rfl
end Sum

lemma gaussianLogPartition_measurable_finite {I S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) :
    Measurable (fun g=>Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)) := by
  apply Measurable.log
  have hm : Measurable (fun p : EuclideanSpace ℝ I×S=>H p.2+inner ℝ (V p.2) p.1) :=
    (hH.comp measurable_snd).add ((hV.comp measurable_snd).inner measurable_fst)
  simpa only [tiltPartition,one_mul] using hm.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma gaussianInl_log_integral {I J S : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) :
    (∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (gaussianInl (J:=J) (V s)) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ (I⊕J)))=
    ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ I) := by
  simp_rw [gaussianInl_linear]
  have hp : MeasurePreserving (fun g : EuclideanSpace ℝ (I⊕J)=>(gaussianSumSplit g).1)
      (stdGaussian (EuclideanSpace ℝ (I⊕J))) (stdGaussian (EuclideanSpace ℝ I)) :=
    measurePreserving_fst.comp gaussianSumSplit_preserving
  have he:=integral_map (μ:=stdGaussian (EuclideanSpace ℝ (I⊕J))) hp.measurable.aemeasurable (gaussianLogPartition_measurable_finite μ hH hV).aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

lemma gaussianInr_log_integral {I J S : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ J}
    (hH : Measurable H) (hV : Measurable V) :
    (∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (gaussianInr (I:=I) (V s)) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ (I⊕J)))=
    ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ J) := by
  simp_rw [gaussianInr_linear]
  have hp : MeasurePreserving (fun g : EuclideanSpace ℝ (I⊕J)=>(gaussianSumSplit g).2)
      (stdGaussian (EuclideanSpace ℝ (I⊕J))) (stdGaussian (EuclideanSpace ℝ J)) :=
    measurePreserving_snd.comp gaussianSumSplit_preserving
  have he:=integral_map (μ:=stdGaussian (EuclideanSpace ℝ (I⊕J))) hp.measurable.aemeasurable (gaussianLogPartition_measurable_finite μ hH hV).aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

theorem independentGaussian_covariance_comparison {I J S : Type} [Fintype I] [Fintype J]
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {H : S→ℝ} {V : S→EuclideanSpace ℝ I} {W : S→EuclideanSpace ℝ J}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A C ε : ℝ} (hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
    (hVC : ∀ s,‖V s‖≤C) (hWC : ∀ s,‖W s‖≤C) (hε : 0≤ε)
    (hcov : ∀ x y,|inner ℝ (W x) (W y)-inner ℝ (V x) (V y)|≤ε) :
    |(∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (W s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ J))-
      ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ I)|≤Real.pi*ε := by
  have hv : Measurable (fun s=>gaussianInl (J:=J) (V s)) := gaussianInl_measurable.comp hV
  have hw : Measurable (fun s=>gaussianInr (I:=I) (W s)) := gaussianInr_measurable.comp hW
  have ht:=euclideanGaussian_covariance_comparison μ hH hv hw hA hC hHA
    (fun s=>by simpa only [gaussianInl_norm] using hVC s)
    (fun s=>by simpa only [gaussianInr_norm] using hWC s) hε
    (fun x y=>gaussianInl_Inr_inner (V x) (W y))
    (fun x y=>by simpa only [gaussianInr_inner,gaussianInl_inner] using hcov x y)
  rwa [gaussianInl_log_integral μ hH hV,gaussianInr_log_integral μ hH hW] at ht

end SphericalPerceptronFreeEnergy
end

end OAI
