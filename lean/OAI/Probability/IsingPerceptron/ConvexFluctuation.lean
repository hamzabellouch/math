import Mathlib
import OAI.Probability.IsingPerceptron.FullPerturbation

namespace OAI

/-! Convex Fluctuation. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval

lemma convex_derivative_deviation {p F dp dF : ℝ → ℝ}
    (hp : ConvexOn ℝ univ p) (hF : ConvexOn ℝ univ F)
    (hdp : ∀u,HasDerivAt p (dp u) u) (hdF : ∀u,HasDerivAt F (dF u) u)
    (v : ℝ) {η : ℝ} (hη : 0<η) :
    |dp v-dF v| ≤
      (|p (v+η)-F (v+η)|+2*|p v-F v|+|p (v-η)-F (v-η)|)/η+
      (dF (v+η)-dF (v-η)) := by
  have h1 := hp.le_slope_of_hasDerivAt (mem_univ v) (mem_univ (v+η)) (by linarith) (hdp v)
  have h2 := hp.slope_le_of_hasDerivAt (mem_univ (v-η)) (mem_univ v) (by linarith) (hdp v)
  have h3 := hF.slope_le_of_hasDerivAt (mem_univ v) (mem_univ (v+η)) (by linarith) (hdF (v+η))
  have h4 := hF.le_slope_of_hasDerivAt (mem_univ (v-η)) (mem_univ v) (by linarith) (hdF (v-η))
  simp only [slope_def_field,add_sub_cancel_left,sub_sub_cancel] at h1 h2 h3 h4
  have hm : Monotone dF := by
    intro x y hxy
    have h := hF.monotoneOn_deriv (fun u _ => (hdF u).differentiableAt) (mem_univ x) (mem_univ y) hxy
    simpa only [(hdF x).deriv,(hdF y).deriv] using h
  have hm1 := hm (show v-η≤v by linarith)
  have hm2 := hm (show v≤v+η by linarith)
  rw [le_div_iff₀ hη] at h1 h4
  rw [div_le_iff₀ hη] at h2 h3
  rw [← sub_le_iff_le_add,le_div_iff₀ hη]
  rcases le_total (dp v) (dF v) with hh | hh
  · rw [abs_of_nonpos (sub_nonpos.mpr hh)]
    nlinarith [le_abs_self (p v-F v),neg_le_abs (p v-F v),
      le_abs_self (p (v-η)-F (v-η)),neg_le_abs (p (v-η)-F (v-η)),
      abs_nonneg (p (v+η)-F (v+η)),abs_nonneg (p v-F v)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hh)]
    nlinarith [le_abs_self (p v-F v),neg_le_abs (p v-F v),
      le_abs_self (p (v+η)-F (v+η)),neg_le_abs (p (v+η)-F (v+η)),
      abs_nonneg (p (v-η)-F (v-η)),abs_nonneg (p v-F v)]

lemma integrated_derivative_shift_le {F dF : ℝ → ℝ}
    (hdF : ∀u,HasDerivAt F (dF u) u) (hc : Continuous dF)
    {η B : ℝ} (hη : 0≤η) (hη' : η≤1/2)
    (hB : ∀u ∈ Icc (1/2:ℝ) (5/2),|dF u|≤B) :
    (∫u in (1:ℝ)..2,(dF (u+η)-dF (u-η)))≤4*η*B := by
  have hp : IntervalIntegrable (fun u => dF (u+η)) volume 1 2 :=
    (hc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hm : IntervalIntegrable (fun u => dF (u-η)) volume 1 2 :=
    (hc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hp hm,intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_comp_sub_right,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hdF u) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hdF u) (hc.intervalIntegrable _ _)]
  have h2 := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=2-η) (b:=2+η) (f:=F) (f':=dF) (C:=B)
    (fun u _ => (hdF u).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hB u ⟨by linarith [hu.1],by linarith [hu.2]⟩)
    (2+η) ⟨by linarith,le_rfl⟩
  have h1 := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=1-η) (b:=1+η) (f:=F) (f':=dF) (C:=B)
    (fun u _ => (hdF u).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hB u ⟨by linarith [hu.1],by linarith [hu.2]⟩)
    (1+η) ⟨by linarith,le_rfl⟩
  simp only [Real.norm_eq_abs] at h1 h2
  linarith [le_abs_self (F (2+η)-F (2-η)),neg_le_abs (F (1+η)-F (1-η))]

lemma integral_abs_centered_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫ω,|X ω-∫z,X z ∂μ| ∂μ)≤ sqrt (variance X μ) := by
  have hz : MemLp (fun ω => |X ω-∫z,X z ∂μ|) 2 μ := (hX.sub (memLp_const _)).abs
  have hv := variance_nonneg (fun ω => |X ω-∫z,X z ∂μ|) μ
  rw [variance_eq_sub hz] at hv
  simp only [Pi.pow_apply,sq_abs] at hv
  rw [← variance_eq_integral hX.aemeasurable] at hv
  exact (le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg X μ)).mpr (by linarith)

lemma expected_convex_derivative_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p dp : ℝ → Ω → ℝ) (F dF : ℝ → ℝ)
    (hp : ∀ω,ConvexOn ℝ univ (fun u => p u ω)) (hF : ConvexOn ℝ univ F)
    (hdp : ∀u ω,HasDerivAt (fun v => p v ω) (dp u ω) u)
    (hdF : ∀u,HasDerivAt F (dF u) u)
    (hi : ∀u,Integrable (p u) μ) (hid : ∀u,Integrable (dp u) μ)
    (v : ℝ) {η ε : ℝ} (hη : 0<η)
    (he : ∀u ∈ Icc (v-η) (v+η),(∫ω,|p u ω-F u| ∂μ)≤ε) :
    (∫ω,|dp v ω-dF v| ∂μ)≤4*ε/η+(dF (v+η)-dF (v-η)) := by
  have hmono := integral_mono ((hid v).sub (integrable_const _)).abs
    (((((hi (v+η)).sub (integrable_const _)).abs.add (((hi v).sub (integrable_const _)).abs.const_mul 2)).add
      ((hi (v-η)).sub (integrable_const _)).abs).div_const η |>.add (integrable_const _))
    (fun ω => convex_derivative_deviation (hp ω) hF
      (fun u => hdp u ω) hdF v hη)

  simp only [Pi.add_apply,Pi.sub_apply] at hmono
  have hip : Integrable (fun ω => |p (v+η) ω-F (v+η)|) μ := ((hi (v+η)).sub (integrable_const _)).abs
  have hi0 : Integrable (fun ω => 2*|p v ω-F v|) μ := ((hi v).sub (integrable_const _)).abs.const_mul 2
  have him : Integrable (fun ω => |p (v-η) ω-F (v-η)|) μ := ((hi (v-η)).sub (integrable_const _)).abs
  have hia : Integrable (fun ω => |p (v+η) ω-F (v+η)|+2*|p v ω-F v|) μ := hip.add hi0
  have hib : Integrable (fun ω => |p (v+η) ω-F (v+η)|+2*|p v ω-F v|+|p (v-η) ω-F (v-η)|) μ := hia.add him
  rw [integral_add (f:=fun ω => (|p (v+η) ω-F (v+η)|+2*|p v ω-F v|+|p (v-η) ω-F (v-η)|)/η)
      (g:=fun _ => dF (v+η)-dF (v-η)) (hib.div_const η) (integrable_const _),
    integral_div,
    integral_add (f:=fun ω => |p (v+η) ω-F (v+η)|+2*|p v ω-F v|)
      (g:=fun ω => |p (v-η) ω-F (v-η)|) hia him,
    integral_add (f:=fun ω => |p (v+η) ω-F (v+η)|) (g:=fun ω => 2*|p v ω-F v|) hip hi0,
    integral_const_mul,integral_const] at hmono
  simp only [probReal_univ,one_smul] at hmono
  have hpε := he (v+η) ⟨by linarith,le_rfl⟩
  have h0ε := he v ⟨by linarith,by linarith⟩
  have hmε := he (v-η) ⟨le_rfl,by linarith⟩
  apply hmono.trans
  exact add_le_add (div_le_div_of_nonneg_right (by linarith) hη.le) le_rfl

theorem integrated_convex_derivative_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p dp : ℝ → Ω → ℝ) (F dF : ℝ → ℝ)
    (hp : ∀ω,ConvexOn ℝ univ (fun u => p u ω)) (hF : ConvexOn ℝ univ F)
    (hdp : ∀u ω,HasDerivAt (fun v => p v ω) (dp u ω) u)
    (hdF : ∀u,HasDerivAt F (dF u) u) (hc : Continuous dF)
    (hi : ∀u,Integrable (p u) μ) (hid : ∀u,Integrable (dp u) μ)
    (hiabs : IntervalIntegrable (fun u => ∫ω,|dp u ω-dF u| ∂μ) volume 1 2)
    {η ε B : ℝ} (hη : 0<η) (hη' : η≤1/2)
    (he : ∀u ∈ Icc (1/2:ℝ) (5/2),(∫ω,|p u ω-F u| ∂μ)≤ε)
    (hB : ∀u ∈ Icc (1/2:ℝ) (5/2),|dF u|≤B) :
    (∫u in (1:ℝ)..2,∫ω,|dp u ω-dF u| ∂μ)≤4*ε/η+4*η*B := by
  have hs : IntervalIntegrable (fun u => dF (u+η)-dF (u-η)) volume 1 2 :=
    ((hc.comp (continuous_id.add continuous_const)).sub
      (hc.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ)≤2) hiabs
    (intervalIntegrable_const.add hs) (fun v hv =>
      expected_convex_derivative_deviation μ p dp F dF hp hF hdp hdF hi hid v hη
        (fun u hu => he u ⟨by linarith [hv.1,hu.1],by linarith [hv.2,hu.2]⟩))
  rw [intervalIntegral.integral_add intervalIntegrable_const hs,intervalIntegral.integral_const] at h
  norm_num at h
  linarith [integrated_derivative_shift_le hdF hc hη.le hη' hB]

variable {S : Type*} [Fintype S] [Nonempty S]

lemma gaussian_logPartition_convex {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (g : Fin (m+1) → ℝ) :
    ConvexOn ℝ univ (fun t => finiteLogPartition (gaussianGibbsH W A t g)) := by
  have hm := monotone_of_hasDerivAt_nonneg
    (fun t => gaussian_parameter_thermal_derivative W A g t)
    (fun t => gaussianThermalVariance_nonneg W A t g)
  apply Monotone.convexOn_univ_of_deriv (fun t => (gaussian_parameter_derivative W A g t).differentiableAt)
  intro x y hxy
  rw [(gaussian_parameter_derivative W A g x).deriv,(gaussian_parameter_derivative W A g y).deriv]
  exact hm hxy

lemma mean_gaussian_logPartition_convex {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ) :
    ConvexOn ℝ univ (fun t => ∫g,finiteLogPartition (gaussianGibbsH W A t g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hm := monotone_of_hasDerivAt_nonneg
    (fun t => mean_gaussian_thermal_derivative W A t)
    (fun t => integral_nonneg (fun g => gaussianThermalVariance_nonneg W A t g))
  apply Monotone.convexOn_univ_of_deriv (fun t => (mean_gaussian_parameter_derivative W A t).differentiableAt)
  intro x y hxy
  rw [(mean_gaussian_parameter_derivative W A x).deriv,(mean_gaussian_parameter_derivative W A y).deriv]
  exact hm hxy

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology
variable {S : Type*} [Fintype S] [Nonempty S]

lemma gaussian_perturbation_mean_cost {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ)
    {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i) :
    |(∫g,linearLogPartition W A g ∂Measure.pi (fun _ => gaussianReal 0 1))-
      finiteLogPartition W| ≤ 2*∑i,c i^2 := by
  cases n with
  | zero =>
    simp [linearLogPartition]
  | succ m =>
    let F : ℝ → ℝ := fun t => ∫g,finiteLogPartition (gaussianGibbsH W A t g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)
    let dF : ℝ → ℝ := fun t => ∫g,finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)
    have hd : ∀u,HasDerivAt F (dF u) u := mean_gaussian_parameter_derivative W A
    have hb : ∀u ∈ Ico (0:ℝ) 1,‖dF u‖≤2*∑i,c i^2 := by
      intro u hu
      rw [Real.norm_eq_abs]
      have h := gaussian_mean_energy_bound W A hc u
      rw [abs_of_nonneg hu.1] at h
      exact h.trans (by nlinarith [hu.2,Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (c i))])
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u (_ : u∈Icc (0:ℝ) 1) => (hd u).hasDerivWithinAt) hb 1 ⟨zero_le_one,le_rfl⟩
    have h0 : F 0=finiteLogPartition W := by
      have he (g : Fin (m+1) → ℝ) : gaussianGibbsH W A 0 g=W := by funext x; simp [gaussianGibbsH]
      simp only [F,he,integral_const,probReal_univ,one_smul]
    have h1 : F 1=∫g,linearLogPartition W A g ∂Measure.pi (fun _ => gaussianReal 0 1) := by
      have he (g : Fin (m+1) → ℝ) : gaussianGibbsH W A 1 g=(fun x => W x+∑i,g i*A x i) := by
        funext x
        simp only [gaussianGibbsH,one_mul,gaussianLinear]
      change (∫g,finiteLogPartition (gaussianGibbsH W A 1 g) ∂Measure.pi (fun _ => gaussianReal 0 1))= _
      simp only [he,linearLogPartition]
    simpa only [h0,h1,Real.norm_eq_abs,sub_zero,mul_one] using h

lemma random_linearLogPartition_memLp {R : Type*} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] {n : ℕ} (W : R → S → ℝ)
    (hmW : ∀x,Measurable (fun r => W r x)) (A : S → Fin n → ℝ)
    {M : ℝ} (hW : ∀r x,|W r x|≤M) {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i) :
    MemLp (fun p : (Fin n → ℝ) × R => linearLogPartition (W p.2) A p.1) 2
      ((Measure.pi (fun _ => gaussianReal 0 1)).prod ν) := by
  let B : (Fin n → ℝ) → ℝ := fun g => M+∑i,c i*|g i|
  have hiB : MemLp B 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
    exact (memLp_const M).add (memLp_finsetSum _ (fun i _ =>
      ((memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).abs.const_mul (c i)))
  apply (hiB.comp_measurePreserving measurePreserving_fst).mono
    (by unfold linearLogPartition finiteLogPartition; fun_prop : Measurable _).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    simp only [Function.comp_apply,Real.norm_eq_abs]
    exact (linearLogPartition_bound (W p.2) A (hW p.2) hc p.1).trans (le_abs_self _)

theorem random_gaussian_perturbation_mean_cost {R : Type*} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] {n : ℕ} (W : R → S → ℝ)
    (hmW : ∀x,Measurable (fun r => W r x)) (A : S → Fin n → ℝ)
    {M : ℝ} (hW : ∀r x,|W r x|≤M) {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i) :
    |(∫p : (Fin n → ℝ) × R,linearLogPartition (W p.2) A p.1
        ∂(Measure.pi (fun _ => gaussianReal 0 1)).prod ν)-
      (∫r,finiteLogPartition (W r) ∂ν)| ≤ 2*∑i,c i^2 := by
  have hi := (random_linearLogPartition_memLp ν W hmW A hW hc).integrable (by norm_num)
  have hWm : Measurable (fun r => finiteLogPartition (W r)) := by unfold finiteLogPartition; fun_prop
  have hWi : Integrable (fun r => finiteLogPartition (W r)) ν :=
    (bounded_memLp ν hWm (fun r => finite_log_average_abs (W r) M (hW r))).integrable (by norm_num)
  rw [integral_prod_symm _ hi,← integral_sub hi.integral_prod_right hWi]
  exact bounded_mean ν (fun r => gaussian_perturbation_mean_cost (W r) A hc)

theorem actual_perturbation_mean_cost {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (s : ℝ) (v : ℕ → ℝ) :
    |(∫p,perturbedLogPartition (M:=M) hN f s v p ∂perturbedDisorderLaw M N)-
      (∫g,finiteLogPartition (patternEnergy (M:=M) (N:=N) f g)
        ∂Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)))| ≤
      2*∑j : Fin N,(tensorAmplitude s v (j.val+1))^2 := by
  have h := random_gaussian_perturbation_mean_cost
    (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)))
    (patternEnergy f) (fun x => by unfold patternEnergy rowEvaluation; fun_prop)
    (fullTensorCoefficient hN s v) (patternEnergy_bound hC)
    (fun x i => (fullTensorCoefficient_abs hN s v x i).le)
  rw [fullTensorBound_squares hN s v] at h
  exact h

def fullPerturbedPressure (α : ℝ) {N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (v : ℕ → ℝ)
    (p : PerturbedDisorder (patternCount α N) N) : ℝ :=
  perturbedLogPartition hN f (perturbationScale N) v p/N

lemma perturbationScale_sq_div {N : ℕ} (hN : 0<N) :
    (perturbationScale N)^2/(N:ℝ)=(N:ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  unfold perturbationScale
  rw [← rpow_natCast,← rpow_mul hn.le]
  norm_num
  calc (N:ℝ)^((3:ℝ)/4)/(N:ℝ)=(N:ℝ)^((3:ℝ)/4)/(N:ℝ)^(1:ℝ) := by rw [rpow_one]
    _ = _ := by rw [← rpow_sub hn]; norm_num

theorem fullPerturbedPressure_mean_cost (α : ℝ) {N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Icc (1/2:ℝ) (5/2)) :
    |(∫p,fullPerturbedPressure α hN f v p ∂perturbedDisorderLaw (patternCount α N) N)-
      meanPressure α f N| ≤ (25/6)*(N:ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := actual_perturbation_mean_cost (M:=patternCount α N) hN hf hC (perturbationScale N) v
  have hb := totalTensor_variance_uniform (perturbationScale N) v hv
  have hp (g : Disorder α N) : pressure α f N g=finiteLogPartition (patternEnergy f g)/N := by
    unfold pressure partitionFunction finiteLogPartition patternEnergy patternEvaluation rowEvaluation
    rw [spin_card]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
  change |(∫p,perturbedLogPartition hN f (perturbationScale N) v p/N
      ∂perturbedDisorderLaw (patternCount α N) N)-(∫g,pressure α f N g ∂disorderLaw α N)|≤_
  simp_rw [hp]
  rw [integral_div,integral_div,← sub_div,abs_div,abs_of_pos hn]
  calc _ ≤ (2*∑j : Fin N,(tensorAmplitude (perturbationScale N) v (j.val+1))^2)/N :=
      div_le_div_of_nonneg_right h hn.le
    _ ≤ ((25/6)*(perturbationScale N)^2)/N :=
      div_le_div_of_nonneg_right (by linarith) hn.le
    _ = _ := by rw [mul_div_assoc,perturbationScale_sq_div hN]

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval
variable {S R : Type*} [Fintype S] [Nonempty S] [MeasurableSpace R]

abbrev affineDisorderLaw (m : ℕ) (ν : Measure R) : Measure ((Fin (m+1) → ℝ) × R) :=
  (Measure.pi (fun _ => gaussianReal 0 1)).prod ν

def affineHamiltonian {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) (x : S) : ℝ :=
  W p.2 x+gaussianLinear B p.1 x+u*gaussianLinear A p.1 x

def affineLogPartition {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : ℝ := finiteLogPartition (affineHamiltonian W B A u p)

def affineEnergy {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : ℝ :=
  finiteGibbs (affineHamiltonian W B A u p) (gaussianLinear A p.1)

def affineThermal {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : ℝ :=
  finiteGibbs (affineHamiltonian W B A u p) (fun x =>
    (gaussianLinear A p.1 x-affineEnergy W B A u p)^2)

omit [Fintype S] [Nonempty S] [MeasurableSpace R] in
lemma affineHamiltonian_eq {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) :
    affineHamiltonian W B A u p=gaussianGibbsH (W p.2) (fun x i => B x i+u*A x i) 1 p.1 := by
  funext x
  simp only [affineHamiltonian,gaussianGibbsH,one_mul,gaussianLinear,Finset.mul_sum,Finset.sum_add_distrib,mul_add]
  rw [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [MeasurableSpace R] in
lemma affineLogPartition_derivative {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (p : (Fin (m+1) → ℝ) × R) (u : ℝ) :
    HasDerivAt (fun v => affineLogPartition W B A v p) (affineEnergy W B A u p) u := by
  exact gaussian_parameter_derivative (fun x => W p.2 x+gaussianLinear B p.1 x) A p.1 u

omit [MeasurableSpace R] in
lemma affineEnergy_derivative {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (p : (Fin (m+1) → ℝ) × R) (u : ℝ) :
    HasDerivAt (fun v => affineEnergy W B A v p) (affineThermal W B A u p) u := by
  exact gaussian_parameter_thermal_derivative (fun x => W p.2 x+gaussianLinear B p.1 x) A p.1 u

omit [MeasurableSpace R] in
lemma affineEnergy_bound {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : |affineEnergy W B A u p|≤gaussianLinearBound A p.1 :=
  finiteGibbs_abs _ _ (gaussianLinear_abs_bound A p.1)

omit [MeasurableSpace R] in
lemma affineThermal_bound {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : |affineThermal W B A u p|≤(gaussianLinearBound A p.1)^2 :=
  gaussianThermalVariance_bound (fun x => W p.2 x+gaussianLinear B p.1 x) A u p.1

omit [Nonempty S] in
lemma affineEnergy_measurable {m : ℕ} (W : R → S → ℝ)
    (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) :
    Measurable (fun p : ℝ × ((Fin (m+1) → ℝ) × R) => affineEnergy W B A p.1 p.2) := by
  unfold affineEnergy finiteGibbs affineHamiltonian gaussianLinear
  fun_prop

omit [Nonempty S] in
lemma affineThermal_measurable {m : ℕ} (W : R → S → ℝ)
    (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) :
    Measurable (fun p : ℝ × ((Fin (m+1) → ℝ) × R) => affineThermal W B A p.1 p.2) := by
  unfold affineThermal affineEnergy finiteGibbs affineHamiltonian gaussianLinear
  fun_prop

lemma affineEnergy_integrable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) (u : ℝ) :
    Integrable (affineEnergy W B A u) (affineDisorderLaw m ν) := by
  apply ((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num) |>.mono'
      (((affineEnergy_measurable W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using affineEnergy_bound W B A u p

lemma affineThermal_integrable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) (u : ℝ) :
    Integrable (affineThermal W B A u) (affineDisorderLaw m ν) := by
  apply (((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable_sq).mono'
      (((affineThermal_measurable W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using affineThermal_bound W B A u p

lemma affineLogPartition_memLp {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ)
    {M : ℝ} (hW : ∀r x,|W r x|≤M) (u : ℝ) :
    MemLp (affineLogPartition W B A u) 2 (affineDisorderLaw m ν) := by
  have he : affineLogPartition W B A u=fun p => linearLogPartition (W p.2) (fun x i => B x i+u*A x i) p.1 := by
    funext p
    unfold affineLogPartition
    rw [affineHamiltonian_eq]
    congr 1
    funext x
    simp [gaussianGibbsH,gaussianLinear]
  rw [he]
  exact random_linearLogPartition_memLp ν W hmW _ hW (fun x i => finiteFunction_bound (fun x => B x i+u*A x i) x)

lemma mean_affineLogPartition_derivative {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ)
    {M : ℝ} (hW : ∀r x,|W r x|≤M) (t : ℝ) :
    HasDerivAt (fun u => ∫p,affineLogPartition W B A u p ∂affineDisorderLaw m ν)
      (∫p,affineEnergy W B A t p ∂affineDisorderLaw m ν) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=Set.univ)
    (bound:=fun p => gaussianLinearBound A p.1) (F':=fun u p => affineEnergy W B A u p) (Filter.univ_mem)
    (Eventually.of_forall (fun u => (show Measurable (affineLogPartition W B A u) from by
      unfold affineLogPartition finiteLogPartition affineHamiltonian gaussianLinear; fun_prop).aestronglyMeasurable))
    ((affineLogPartition_memLp ν W hmW B A hW t).integrable (by norm_num))
    (((affineEnergy_measurable W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun p u _ => by simpa only [Real.norm_eq_abs] using affineEnergy_bound W B A u p)
    (((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable (by norm_num))
    (ae_of_all _ fun p u _ => affineLogPartition_derivative W B A p u)).2

lemma mean_affineEnergy_derivative {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ∫p,affineEnergy W B A u p ∂affineDisorderLaw m ν)
      (∫p,affineThermal W B A t p ∂affineDisorderLaw m ν) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=Set.univ)
    (F:=fun u p => affineEnergy W B A u p)
    (bound:=fun p => (gaussianLinearBound A p.1)^2) (F':=fun u p => affineThermal W B A u p) (Filter.univ_mem)
    (Eventually.of_forall (fun u =>
      (((affineEnergy_measurable W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)))
    (affineEnergy_integrable ν W hmW B A t)
    (((affineThermal_measurable W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun p u _ => by simpa only [Real.norm_eq_abs] using affineThermal_bound W B A u p)
    (((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable_sq)
    (ae_of_all _ fun p u _ => affineEnergy_derivative W B A p u)).2

lemma gaussian_orthogonal_mean_energy_bound {m : ℕ} (W : S → ℝ)
    (B A : S → Fin (m+1) → ℝ)
    (hAB : ∀x y,∑i,A x i*B y i=0) {c : Fin (m+1) → ℝ}
    (hc : ∀x i,|A x i|≤c i) (u : ℝ) :
    |∫g,finiteGibbs (gaussianGibbsH W (fun x i => B x i+u*A x i) 1 g)
      (gaussianLinear A g) ∂Measure.pi (fun _ => gaussianReal 0 1)|≤2*|u| *(∑i,c i^2) := by
  have he := gaussianGibbs_ibp W (fun _ => 1) (fun x i => B x i+u*A x i) A 1
  have hs (x y : S) : (∑i,A x i*(B y i+u*A y i))=u*∑i,A x i*A y i := by
    simp only [mul_add,Finset.sum_add_distrib,hAB,zero_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [one_mul,hs,finiteGibbs_const_mul,finiteGibbsPair] at he
  rw [he]
  apply bounded_mean
  intro g
  rw [← mul_sub,abs_mul]
  let H := gaussianGibbsH W (fun x i => B x i+u*A x i) 1 g
  have hd := finiteGibbs_abs H (fun x => ∑i,A x i*A x i)
    (fun x => coefficient_cov_bound A hc x x)
  have hr := finiteGibbs_abs H
    (fun x => finiteGibbs H (fun y => ∑i,A x i*A y i))
    (fun x => finiteGibbs_abs _ _ (fun y => coefficient_cov_bound A hc x y))
  have hb := (abs_sub _ _).trans (add_le_add hd hr)
  calc _ ≤ |u| *((∑i,c i^2)+(∑i,c i^2)) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

theorem affine_mean_energy_bound {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin (m+1) → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {c : Fin (m+1) → ℝ} (hc : ∀x i,|A x i|≤c i) (u : ℝ) :
    |∫p,affineEnergy W B A u p ∂affineDisorderLaw m ν|≤2*|u| *(∑i,c i^2) := by
  rw [integral_prod_symm _ (affineEnergy_integrable ν W hmW B A u)]
  apply bounded_mean ν
  intro r
  have he : (fun g => affineEnergy W B A u (g,r))=fun g =>
      finiteGibbs (gaussianGibbsH (W r) (fun x i => B x i+u*A x i) 1 g) (gaussianLinear A g) := by
    funext g
    unfold affineEnergy
    rw [affineHamiltonian_eq]
  rw [he]
  exact gaussian_orthogonal_mean_energy_bound (W r) B A hAB hc u

omit [MeasurableSpace R] in
lemma affineLogPartition_convex {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (p : (Fin (m+1) → ℝ) × R) : ConvexOn ℝ univ (fun u => affineLogPartition W B A u p) :=
  gaussian_logPartition_convex (fun x => W p.2 x+gaussianLinear B p.1 x) A p.1

lemma mean_affineLogPartition_convex {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ)
    {M : ℝ} (hW : ∀r x,|W r x|≤M) :
    ConvexOn ℝ univ (fun u => ∫p,affineLogPartition W B A u p ∂affineDisorderLaw m ν) := by
  have hm := monotone_of_hasDerivAt_nonneg
    (fun t => mean_affineEnergy_derivative ν W hmW B A t)
    (fun t => integral_nonneg (fun p => finiteGibbs_nonneg _ _ (fun x => sq_nonneg _)))
  apply Monotone.convexOn_univ_of_deriv
    (fun t => (mean_affineLogPartition_derivative ν W hmW B A hW t).differentiableAt)
  intro x y hxy
  rw [(mean_affineLogPartition_derivative ν W hmW B A hW x).deriv,
    (mean_affineLogPartition_derivative ν W hmW B A hW y).deriv]
  exact hm hxy

lemma affine_centeredEnergy_intervalIntegrable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) :
    IntervalIntegrable (fun u => ∫p,|affineEnergy W B A u p-
      ∫q,affineEnergy W B A u q ∂affineDisorderLaw m ν| ∂affineDisorderLaw m ν) volume 1 2 := by
  let μ := affineDisorderLaw m ν
  let L : ℝ := ∫p,gaussianLinearBound A p.1 ∂μ
  have hiL : Integrable (fun p => gaussianLinearBound A p.1) μ :=
    ((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable (by norm_num)
  have hmF : Measurable (fun u => ∫q,affineEnergy W B A u q ∂μ) :=
    (affineEnergy_measurable W hmW B A).stronglyMeasurable.integral_prod_right.measurable
  have hm : Measurable (fun p : ℝ × ((Fin (m+1) → ℝ) × R) =>
      |affineEnergy W B A p.1 p.2-∫q,affineEnergy W B A p.1 q ∂μ|) :=
    ((affineEnergy_measurable W hmW B A).sub (hmF.comp measurable_fst)).abs
  apply (intervalIntegrable_const (c:=2*L)).mono_fun
    hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards [] with u
  have hE := affineEnergy_integrable ν W hmW B A u
  have he : |∫q,affineEnergy W B A u q ∂μ|≤L := by
    calc _ ≤ ∫q,|affineEnergy W B A u q| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (affineEnergy W B A u)
      _ ≤ L := integral_mono hE.abs hiL (affineEnergy_bound W B A u)
  have h := integral_mono (hE.sub (integrable_const _)).abs (hiL.add (integrable_const L))
    (fun p => (abs_sub _ _).trans (add_le_add (affineEnergy_bound W B A u p) he))
  simp only [Pi.add_apply,Pi.sub_apply] at h
  rw [integral_add (μ:=μ) (f:=fun p : (Fin (m+1) → ℝ) × R => gaussianLinearBound A p.1) (g:=fun _ => L) hiL (integrable_const L),
    integral_const] at h
  simp only [probReal_univ,one_smul] at h
  simpa only [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using
    h.trans (show L+L≤|2*L| by simpa only [two_mul] using le_abs_self (L+L))

theorem orthogonal_block_quenched_integral {m n : ℕ} [Nonempty R]
    (ν : Fin n → Measure R) [∀i,IsProbabilityMeasure (ν i)]
    (W : (Fin n → R) → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin (m+1) → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {M : ℝ} (hW : ∀r x,|W r x|≤M)
    {a b : Fin (m+1) → ℝ} (ha : ∀x i,|A x i|≤a i)
    (hb : ∀u ∈ Icc (1/2:ℝ) (5/2),∀x i,|B x i+u*A x i|≤b i)
    (d : Fin n → ℝ) (hd : ∀i r r',(∀k,k≠i → r k=r' k) → ∀x,|W r x-W r' x|≤d i)
    {η : ℝ} (hη : 0<η) (hη' : η≤1/2) :
    (∫u in (1:ℝ)..2,∫p,|affineEnergy W B A u p-
      ∫q,affineEnergy W B A u q ∂affineDisorderLaw m (Measure.pi ν)|
      ∂affineDisorderLaw m (Measure.pi ν))≤
      4*sqrt ((∑i,b i^2)+(∑i,d i^2))/η+20*η*(∑i,a i^2) := by
  let μ := affineDisorderLaw m (Measure.pi ν)
  let F := fun u => ∫p,affineLogPartition W B A u p ∂μ
  let E := fun u => ∫p,affineEnergy W B A u p ∂μ
  have hp (u) := affineLogPartition_memLp (Measure.pi ν) W hmW B A hW u
  have hF (u) := mean_affineLogPartition_derivative (Measure.pi ν) W hmW B A hW u
  have hE (u) := mean_affineEnergy_derivative (Measure.pi ν) W hmW B A u
  have h := integrated_convex_derivative_deviation μ (affineLogPartition W B A) (affineEnergy W B A) F E
    (affineLogPartition_convex W B A) (mean_affineLogPartition_convex (Measure.pi ν) W hmW B A hW)
    (fun u p => affineLogPartition_derivative W B A p u) hF
    (continuous_iff_continuousAt.mpr (fun u => (hE u).continuousAt))
    (fun u => (hp u).integrable (by norm_num)) (affineEnergy_integrable (Measure.pi ν) W hmW B A)
    (affine_centeredEnergy_intervalIntegrable (Measure.pi ν) W hmW B A) hη hη'
    (ε:=sqrt ((∑i,b i^2)+(∑i,d i^2))) (B:=5*∑i,a i^2) ?_ ?_
  · convert h using 1; ring
  · intro u hu
    apply (integral_abs_centered_le_sqrt_variance (hp u)).trans
    apply Real.sqrt_le_sqrt
    have he : affineLogPartition W B A u=fun p =>
        linearLogPartition (W p.2) (fun x i => B x i+u*A x i) p.1 := by
      funext p
      unfold affineLogPartition
      rw [affineHamiltonian_eq]
      congr 1
      funext x
      simp [gaussianGibbsH,gaussianLinear]
    rw [he]
    exact mixed_logPartition_variance ν W hmW _ hW (hb u hu) d hd
  · intro u hu
    apply (affine_mean_energy_bound (Measure.pi ν) W hmW B A hAB ha u).trans
    have hs : 0≤∑i,a i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [abs_of_nonneg (by linarith [hu.1] : 0≤u)]
    nlinarith [hu.2]

end IsingPerceptron.Main

end

end OAI
