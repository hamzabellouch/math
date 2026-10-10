import Mathlib
import OAI.Probability.SKGap.Localization.Centered
import OAI.Probability.SKGap.Localization.JumpWeight
import OAI.Probability.SKGap.Stability.ConditionalMean

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
open scoped BigOperators
open ContinuousLinearMap
open scoped BigOperators
open ContinuousLinearMap
open scoped Topology Interval
open MeasureTheory
open MeasureTheory
open scoped BigOperators Topology Interval
open MeasureTheory
open scoped BigOperators Topology Interval
open scoped Topology
open MeasureTheory
open scoped BigOperators Topology Interval
open scoped BigOperators Topology
open MeasureTheory
open scoped BigOperators Topology Interval RealInnerProductSpace
open MeasureTheory Filter
open scoped BigOperators Topology Interval
namespace SKGapCutoff

lemma jumpWeight_conditional_first {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (i : Fin n) (f : Observables n) (hf : ∀ x, f (flip x i)=f x) :
    gibbsExpectation J (fun x => jumpWeight J x i*f x) =
      gibbsExpectation J (fun x => siteVariance J x i*f x) := by
  have hm := gibbs_coordinate_mean J hJ hdiag i (fun x => mean J x i*f x)
    (fun x => by rw [mean_flip J hdiag,hf])
  have he (x : Spin n) : gibbs J x*(jumpWeight J x i*f x-siteVariance J x i*f x) =
    gibbs J x*mean J x i*(mean J x i*f x)-gibbs J x*spin x i*(mean J x i*f x) := by
    unfold jumpWeight siteVariance
    ring
  have hz : gibbsExpectation J (fun x => jumpWeight J x i*f x)-
      gibbsExpectation J (fun x => siteVariance J x i*f x) = 0 := by
    unfold gibbsExpectation
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub,he]
    rw [Finset.sum_sub_distrib,hm,sub_self]
  linarith

lemma jumpWeight_conditional_square {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (i : Fin n) (f : Observables n) (hf : ∀ x, f (flip x i)=f x) :
    gibbsExpectation J (fun x => (jumpWeight J x i)^2*f x) =
      gibbsExpectation J (fun x => siteVariance J x i*f x) := by
  have hm := gibbs_coordinate_mean J hJ hdiag i (fun x => mean J x i*f x)
    (fun x => by rw [mean_flip J hdiag,hf])
  have he (x : Spin n) : gibbs J x*((jumpWeight J x i)^2*f x-siteVariance J x i*f x) =
    2*(gibbs J x*mean J x i*(mean J x i*f x)-gibbs J x*spin x i*(mean J x i*f x)) := by
    unfold jumpWeight siteVariance
    nlinarith only [congrArg (fun a : ℝ => gibbs J x*(mean J x i)^2*f x*a) (spin_sq x i)]
  have hz : gibbsExpectation J (fun x => (jumpWeight J x i)^2*f x)-
      gibbsExpectation J (fun x => siteVariance J x i*f x) = 0 := by
    unfold gibbsExpectation
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub,he]
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,hm,sub_self,mul_zero]
  linarith

theorem jumpWeight_isometry {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (p : VectorFields n) (hp : ∀ x i, p (flip x i) i=p x i) :
    gibbsExpectation J (vectorSquare (fun x i => jumpWeight J x i*p x i)) =
      weightedInner J p p := by
  unfold vectorSquare weightedInner
  rw [gibbsExpectation_sum,gibbsExpectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := jumpWeight_conditional_square J hJ hdiag i (fun x => (p x i)^2)
    (fun x => by rw [hp])
  convert he using 1 <;> (congr 1; funext x; ring)

lemma exact_gradient_jumpWeight_isometry {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (f : Observables n) :
    gibbsExpectation J (vectorSquare (fun x i => jumpWeight J x i*halfDiff i f x)) =
      dirichlet J f f := by
  exact jumpWeight_isometry J hJ hdiag (fun x i => halfDiff i f x)
    (fun x i => halfDiff_flip i f x)

noncomputable def jumpBilinear {n : ℕ} (J : Interaction n) (f g : Observables n) : Observables n :=
  fun x => 2*∑ i, jumpWeight J x i*halfDiff i f x*halfDiff i g x

lemma backward_product_hasDerivAt {n : ℕ} (J : Interaction n)
    (f g : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => fun x : Spin n =>
      semigroup J (d-r) f x*semigroup J (d-r) g x)
      (fun x => -generator J (semigroup J (d-s) f) x*semigroup J (d-s) g x-
        semigroup J (d-s) f x*generator J (semigroup J (d-s) g) x) s := by
  apply hasDerivAt_pi.mpr
  intro x
  have hh := (hasDerivAt_pi.mp (backward_flow_hasDerivAt J f d s) x).mul
    (hasDerivAt_pi.mp (backward_flow_hasDerivAt J g d s) x)
  convert hh using 1
  ring

lemma interpolated_product_hasDerivAt {n : ℕ} (J : Interaction n)
    (f g : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r (fun x =>
      semigroup J (d-r) f x*semigroup J (d-r) g x))
      (semigroup J s (jumpBilinear J (semigroup J (d-s) f) (semigroup J (d-s) g))) s := by
  have hd := (semigroup_hasDerivAt J s).clm_apply (backward_product_hasDerivAt J f g d s)
  apply hd.congr_deriv
  simp only [mul_apply_eq_comp]
  change semigroup J s (generator J (fun x => semigroup J (d-s) f x*semigroup J (d-s) g x))+
    semigroup J s (fun x => -generator J (semigroup J (d-s) f) x*semigroup J (d-s) g x-
      semigroup J (d-s) f x*generator J (semigroup J (d-s) g) x) = _
  rw [← map_add]
  congr 1
  funext x
  simp only [Pi.add_apply]
  rw [generator_mul]
  simp only [jumpBilinear,jumpWeight]
  ring

lemma jumpBilinear_continuous {n : ℕ} (J : Interaction n) :
    Continuous (fun p : Observables n × Observables n => jumpBilinear J p.1 p.2) := by
  unfold jumpBilinear halfDiff
  fun_prop

lemma interpolated_bilinear_continuous {n : ℕ} (J : Interaction n)
    (f g : Observables n) (d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s
      (jumpBilinear J (semigroup J (d-s) f) (semigroup J (d-s) g)) x) := by
  have hf : Continuous (fun s : ℝ => semigroup J (d-s) f) :=
    ((semigroup_continuous J).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  have hg : Continuous (fun s : ℝ => semigroup J (d-s) g) :=
    ((semigroup_continuous J).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  exact (continuous_apply x).comp ((semigroup_continuous J).clm_apply
    ((jumpBilinear_continuous J).comp (hf.prodMk hg)))

theorem semigroup_covariance_integral {n : ℕ} (J : Interaction n)
    (f g : Observables n) (d : ℝ) (x : Spin n) :
    semigroup J d (fun y => f y*g y) x-semigroup J d f x*semigroup J d g x =
      ∫ s in (0:ℝ)..d, semigroup J s
        (jumpBilinear J (semigroup J (d-s) f) (semigroup J (d-s) g)) x := by
  have hd (s : ℝ) := hasDerivAt_pi.mp (interpolated_product_hasDerivAt J f g d s) x
  have hi := (interpolated_bilinear_continuous J f g d x).intervalIntegrable
    (μ := volume) 0 d
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  simpa only [sub_self,sub_zero,semigroup_zero,one_apply_eq_self] using he.symm

lemma equilibriumPotential_pairing_covariance {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (G : Observables n) (B : VectorFields n) (d : ℝ) :
    stationaryInner J G (equilibriumPotential J d B) = d⁻¹ * ∑ i,
      stationaryInner J (fun x => B x i) (fun x =>
        semigroup J d (fun y => spin y i*G y) x-
          semigroup J d (fun y => spin y i) x*semigroup J d G x) := by
  have hp (i : Fin n) : stationaryInner J (fun x => spin x i*G x)
      (semigroup J d (fun y => B y i)) =
      stationaryInner J (fun x => B x i) (semigroup J d (fun y => spin y i*G y)) := by
    rw [scalar_semigroup_symmetric J hJ hdiag,stationaryInner_symm]
  have hq := scalar_semigroup_symmetric J hJ hdiag d G
    (fun y => ∑ i, semigroup J d (fun z => spin z i) y*B y i)
  unfold stationaryInner at hp hq ⊢
  unfold equilibriumPotential
  simp only [mul_sub,gibbsExpectation_sub,gibbsExpectation_sum,Finset.mul_sum,
    mul_left_comm (G _) d⁻¹, gibbsExpectation_mul_const]
  rw [hq]
  simp only [Finset.mul_sum,gibbsExpectation_sum]
  have hp' (i : Fin n) : gibbsExpectation J (fun x => G x*(spin x i*semigroup J d (fun y => B y i) x)) =
      gibbsExpectation J (fun x => B x i*semigroup J d (fun y => spin y i*G y) x) := by
    simpa only [mul_assoc,mul_comm (G _) (spin _ i),mul_left_comm (G _) (spin _ i)] using hp i
  simp_rw [hp']
  rw [Finset.sum_sub_distrib]
  congr 2
  funext i
  congr 1
  congr 1
  funext x
  ring

lemma semigroup_covariance_zero_hasDerivAt {n : ℕ} (J : Interaction n)
    (f g : Observables n) :
    HasDerivAt (fun d : ℝ => semigroup J d (f*g)-semigroup J d f*semigroup J d g)
      (jumpBilinear J f g) 0 := by
  have hd := (semigroup_apply_hasDerivAt J (f*g) 0).sub
    ((semigroup_apply_hasDerivAt J f 0).mul (semigroup_apply_hasDerivAt J g 0))
  apply hd.congr_deriv
  simp only [semigroup_zero,one_apply_eq_self]
  funext x
  change generator J (fun y => f y*g y) x-
    (generator J f x*g x+f x*generator J g x) = _
  rw [generator_mul]
  dsimp [jumpBilinear,jumpWeight]
  ring

lemma semigroup_covariance_slope {n : ℕ} (J : Interaction n) (f g : Observables n) :
    Tendsto (fun d : ℝ => d⁻¹ • (semigroup J d (f*g)-semigroup J d f*semigroup J d g))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (jumpBilinear J f g)) := by
  simpa only [zero_add,semigroup_zero,one_apply_eq_self,sub_self,sub_zero] using
    (semigroup_covariance_zero_hasDerivAt J f g).tendsto_slope_zero_right

lemma stationaryInner_covariance_slope {n : ℕ} (J : Interaction n)
    (f g b : Observables n) :
    Tendsto (fun d : ℝ => d⁻¹*stationaryInner J b
      (semigroup J d (f*g)-semigroup J d f*semigroup J d g))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (stationaryInner J b (jumpBilinear J f g))) := by
  have hh := (stationaryPairingCLM J b).continuous.tendsto _ |>.comp
    (semigroup_covariance_slope J f g)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,stationaryPairingCLM_apply] using hh

theorem equilibriumPotential_pairing_small_time {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (G : Observables n) (B : VectorFields n) :
    Tendsto (fun d : ℝ => stationaryInner J G (equilibriumPotential J d B))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds
        (2*gibbsExpectation J (fun x => ∑ i, B x i*jumpWeight J x i*halfDiff i G x))) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    stationaryInner_covariance_slope J (fun x => spin x i) G (fun x => B x i))
  have he (d : ℝ) : stationaryInner J G (equilibriumPotential J d B) =
      ∑ i, d⁻¹*stationaryInner J (fun x => B x i)
        (semigroup J d ((fun x => spin x i)*G)-semigroup J d (fun x => spin x i)*semigroup J d G) := by
    rw [equilibriumPotential_pairing_covariance J hJ hdiag,Finset.mul_sum]
    rfl
  simp_rw [he]
  have hl : (∑ i, stationaryInner J (fun x => B x i)
      (jumpBilinear J (fun x => spin x i) G)) =
        2*gibbsExpectation J (fun x => ∑ i, B x i*jumpWeight J x i*halfDiff i G x) := by
    have hj (i : Fin n) : jumpBilinear J (fun x => spin x i) G =
        fun x => 2*jumpWeight J x i*halfDiff i G x := by
      funext x
      simp [jumpBilinear,halfDiff_spin,mul_ite,ite_mul,mul_assoc]
    simp_rw [hj]
    unfold stationaryInner
    rw [← gibbsExpectation_sum,← gibbsExpectation_mul_const]
    congr 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hl]
  exact hh

lemma exact_gradient_pairing_integral {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (G f : Observables n) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, weightedInner J (gradientCLM n G)
      (gradientSemigroup J t (gradientCLM n f))) =
        stationaryInner J G f-stationaryInner J G (semigroup J T f) := by
  have he (t : ℝ) : weightedInner J (gradientCLM n G)
      (gradientSemigroup J t (gradientCLM n f)) =
        -stationaryInner J G (generator J (semigroup J t f)) := by
    change weightedInner J (fun x i => halfDiff i G x)
      (gradientSemigroup J t (fun x i => halfDiff i f x)) = _
    rw [exact_gradient_semigroup_identity J hJ hdiag]
    change stationaryPairingCLM J G (-generator J (semigroup J t f)) = _
    simp only [map_neg,stationaryPairingCLM_apply]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => -stationaryInner J G (semigroup J s f))
      (-stationaryInner J G (generator J (semigroup J t f))) t := by
    exact ((stationaryPairingCLM J G).hasFDerivAt.comp_hasDerivAt t
      (semigroup_apply_hasDerivAt' J f t)).neg
  have hc : Continuous (fun t : ℝ => -stationaryInner J G (generator J (semigroup J t f))) := by
    exact ((stationaryPairingCLM J G).continuous.comp
      ((generatorCLM J).continuous.comp
        ((semigroup_continuous J).clm_apply continuous_const))).neg
  simp_rw [he]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable (μ := volume) 0 T)
  simpa only [semigroup_zero,one_apply_eq_self,sub_neg_eq_add,neg_add_eq_sub] using hh

lemma stationaryInner_centered_semigroup_tendsto_zero {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (G f : Observables n) :
    Tendsto (fun t : ℝ => stationaryInner J G (semigroup J t (centered J f)))
      atTop (nhds 0) := by
  simp_rw [← spectral_parseval J hJ hdiag,spectral_semigroup_coordinates]
  have he (a : Fin (Fintype.card (Spin n))) :
      Tendsto (fun t : ℝ => (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J G) a *
        (Real.exp (-spinEigenvalues J hJ hdiag a*t)*
          (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (centered J f)) a))
        atTop (nhds 0) := by
    by_cases ha : spinEigenvalues J hJ hdiag a=0
    · simp only [centered_spectral_coordinate_zero J hJ hdiag f a ha,mul_zero]
      exact tendsto_const_nhds
    · have hp := lt_of_le_of_ne (spinEigenvalues_nonneg J hJ hdiag a) (Ne.symm ha)
      have hh := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hp))
      simpa only [Function.comp_def,id_eq,zero_mul,mul_zero] using
        (hh.mul_const ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (centered J f)) a)).const_mul
          ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J G) a)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun a _ => he a)

theorem exact_gradient_pairing_integral_tendsto {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    (G f : Observables n) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, weightedInner J (gradientCLM n G)
      (gradientSemigroup J t (gradientCLM n (centered J f)))) atTop
      (nhds (stationaryInner J G (centered J f))) := by
  simp_rw [exact_gradient_pairing_integral J hJ hdiag]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (stationaryInner_centered_semigroup_tendsto_zero J hJ hdiag G f)

lemma centered_semigroup_gap_variance {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    {γ : ℝ} (hγ : HasGap J γ) (f : Observables n) {t : ℝ} (ht : 0 ≤ t) :
    stationaryInner J (semigroup J t (centered J f)) (semigroup J t (centered J f)) ≤
      Real.exp (-2*γ*t)*gibbsVariance J f := by
  rw [← centered_variance,← spectral_parseval J hJ hdiag,← spectral_parseval J hJ hdiag,
    Finset.mul_sum]
  simp_rw [spectral_semigroup_coordinates]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : spinEigenvalues J hJ hdiag a=0
  · simp only [centered_spectral_coordinate_zero J hJ hdiag f a ha,mul_zero,le_refl]
  · have hp := lt_of_le_of_ne (spinEigenvalues_nonneg J hJ hdiag a) (Ne.symm ha)
    have hle := gap_le_positive_eigenvalue J hJ hdiag hγ a hp
    have he : Real.exp (-spinEigenvalues J hJ hdiag a*t)^2 ≤ Real.exp (-2*γ*t) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      norm_num only [Nat.cast_ofNat]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hle) ht]
    have hh := mul_le_mul_of_nonneg_right he
      (sq_nonneg ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (centered J f)) a))
    convert hh using 1 <;> ring

lemma stationaryInner_cauchy_sq {n : ℕ} (J : Interaction n) (f g : Observables n) :
    (stationaryInner J f g)^2 ≤ stationaryInner J f f*stationaryInner J g g := by
  simpa only [stationaryInner,gibbsExpectation,pow_two,mul_assoc] using
    Static.weighted_cauchy_sq (gibbs J) f g (fun x => (gibbs_pos J x).le)

lemma gibbsVariance_nonneg {n : ℕ} (J : Interaction n) (f : Observables n) :
    0 ≤ gibbsVariance J f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (gibbs_pos J x).le (sq_nonneg _))

theorem exact_gradient_pairing_uniform_tail {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j=J j i) (hdiag : ∀ i, J i i=0)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : HasGap J γ)
    (G f : Observables n) {T : ℝ} (hT : 0 ≤ T) :
    γ^2 * (stationaryInner J (centered J G) (centered J f) -
      ∫ t in (0 : ℝ)..T, weightedInner J (gradientCLM n (centered J G))
        (gradientSemigroup J t (gradientCLM n (centered J f))))^2 ≤
      Real.exp (-2*γ*T)*dirichlet J G G*dirichlet J f f := by
  rw [exact_gradient_pairing_integral J hJ hdiag,sub_sub_cancel]
  have hc := stationaryInner_cauchy_sq J (centered J G) (semigroup J T (centered J f))
  rw [centered_variance] at hc
  have he := mul_le_mul_of_nonneg_left (centered_semigroup_gap_variance J hJ hdiag hγ f hT)
    (gibbsVariance_nonneg J G)
  have hsmall := mul_le_mul_of_nonneg_left (hc.trans he) (sq_nonneg γ)
  have hlarge := mul_le_mul (hγ G) (hγ f)
    (mul_nonneg hγ0 (gibbsVariance_nonneg J f)) (dirichlet_nonneg J G)
  have hb := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-2*γ*T)).le
  nlinarith only [hsmall,hb]

end SKGapCutoff

open MeasureTheory Filter
open scoped Topology

end

end OAI
