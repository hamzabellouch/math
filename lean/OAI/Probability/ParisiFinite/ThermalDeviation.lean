import Mathlib
import OAI.Probability.ParisiFinite.IncrementEqKernel

namespace OAI

/-! Thermal Deviation. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiInterpolation ParisiFinite
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

def thermalDeviation (x v : ι → ℝ) : ℝ :=
  ∑ s, weight x s*|v s-gibbsMean 1 x v|

lemma thermalDeviation_nonneg (x v : ι → ℝ) : 0≤thermalDeviation x v :=
  Finset.sum_nonneg fun s _ => mul_nonneg (weight_pos x s).le (abs_nonneg _)

lemma thermalDeviation_le (x v : ι → ℝ) : thermalDeviation x v ≤ 2*‖v‖ := by
  calc
    _ ≤ ∑ s, weight x s*(2*‖v‖) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (weight_pos x s).le
      have h := (norm_le_pi_norm v s)
      have h' := abs_gibbsMean_le 1 x v
      have ht := abs_sub (v s) (gibbsMean 1 x v)
      rw [Real.norm_eq_abs] at h
      linarith
    _ = _ := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma gibbsCov_eq_centered (x v : ι → ℝ) :
    gibbsCov 1 x v v=∑ s, weight x s*(v s-gibbsMean 1 x v)^2 := by
  have he (s : ι) : weight x s*(v s-gibbsMean 1 x v)^2 =
      weight x s*(v s*v s)-2*gibbsMean 1 x v*(weight x s*v s)+
      weight x s*(gibbsMean 1 x v)^2 := by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_weight]
  unfold gibbsCov gibbsMean
  simp only [one_mul]
  ring

lemma thermalDeviation_sq_le (x v : ι → ℝ) :
    (thermalDeviation x v)^2 ≤ gibbsCov 1 x v v := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r:=fun s => weight x s*|v s-gibbsMean 1 x v|)
    (f:=weight x) (g:=fun s => weight x s*(v s-gibbsMean 1 x v)^2)
    (fun s _ => (weight_pos x s).le)
    (fun s _ => mul_nonneg (weight_pos x s).le (sq_nonneg _))
    (fun s _ => by rw [mul_pow, sq_abs]; ring_nf; rfl)
  rw [sum_weight, one_mul, ← gibbsCov_eq_centered] at h
  exact h

lemma continuous_thermalDeviation_field (A B : ι → κ → ℝ) :
    Continuous (fun z => thermalDeviation (field A z) (field B z)) := by
  apply continuous_finsetSum
  intro s _
  apply Continuous.mul ((continuous_weight s).comp (continuous_field A))
  apply Continuous.abs
  apply Continuous.sub ((continuous_apply s).comp (continuous_field B))
  unfold gibbsMean
  apply continuous_finsetSum
  intro t _
  simp only [one_mul]
  exact ((continuous_weight t).comp (continuous_field A)).mul
    ((continuous_apply t).comp (continuous_field B))

lemma memLp_thermalDeviation_field (A B : ι → κ → ℝ) :
    MemLp (fun z => thermalDeviation (field A z) (field B z)) 2 (gaussianLaw κ) := by
  apply ((memLp_norm_field_two B).const_mul 2).mono'
    (continuous_thermalDeviation_field A B).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_of_nonneg (thermalDeviation_nonneg _ _)]
    exact thermalDeviation_le _ _

lemma expected_thermalDeviation_le (A B : ι → κ → ℝ) (t : ℝ) :
    (∫ z, thermalDeviation (field (affineCoeff A B t) z) (field B z) ∂gaussianLaw κ) ≤
      Real.sqrt (varianceLine A B t) := by
  have hm := memLp_thermalDeviation_field (affineCoeff A B t) B
  have hv := variance_nonneg (fun z => thermalDeviation (field (affineCoeff A B t) z) (field B z))
    (gaussianLaw κ)
  rw [variance_eq_sub hm] at hv
  have hi := integral_mono hm.integrable_sq (integrable_lineVariance A B t)
    (fun z => by simpa only [field_affineCoeff] using
      (thermalDeviation_sq_le (field (affineCoeff A B t) z) (field B z)))
  have hs := Real.sq_sqrt (varianceLine_nonneg A B t)
  have hn := Real.sqrt_nonneg (varianceLine A B t)
  change _ ≤ varianceLine A B t at hi
  simp only [Pi.pow_apply] at hv
  nlinarith

 

theorem energyDeviation_le_thermal_add (A B : ι → κ → ℝ) (t c : ℝ) :
    energyDeviation (affineCoeff A B t) B c ≤
      Real.sqrt (varianceLine A B t)+
      ∫ z, |gibbsMean 1 (field A z+t • field B z) (field B z)-c| ∂gaussianLaw κ := by
  have hd (z : κ → ℝ) :
      (∑ s, weight (field (affineCoeff A B t) z) s*|field B z s-c|) ≤
      thermalDeviation (field (affineCoeff A B t) z) (field B z)+
        |gibbsMean 1 (field A z+t • field B z) (field B z)-c| := by
    calc
      _ ≤ ∑ s, weight (field (affineCoeff A B t) z) s*
          (|field B z s-gibbsMean 1 (field A z+t • field B z) (field B z)|+
          |gibbsMean 1 (field A z+t • field B z) (field B z)-c|) := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (weight_pos _ _).le
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_weight, one_mul,
          thermalDeviation, field_affineCoeff]
  have ht := (memLp_thermalDeviation_field (affineCoeff A B t) B).integrable (by norm_num)
  have hc := ((integrable_lineMean A B t).sub (integrable_const c)).abs
  have h := integral_mono (integrable_energyDeviation _ _ c) (ht.add hc) hd
  simp only [Pi.add_apply] at h
  rw [integral_add ht hc] at h
  exact h.trans (add_le_add (expected_thermalDeviation_le A B t) le_rfl)

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiInterpolation ParisiFinite GaussianConcentration
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

def pressureFluctuation (A : ι → κ → ℝ) : ℝ :=
  ∫ z, |logPartition (field A z)-expected A| ∂gaussianLaw κ

def disorderDeviation (A B : ι → κ → ℝ) (t : ℝ) : ℝ :=
  ∫ z, |gibbsMean 1 (field A z+t • field B z) (field B z)-meanLine A B t| ∂gaussianLaw κ

lemma integrable_pressureFluctuation (A : ι → κ → ℝ) :
    Integrable (fun z => |logPartition (field A z)-expected A|) (gaussianLaw κ) := by
  exact (((memLp_logPartition_field A).integrable (by norm_num)).sub (integrable_const _)).abs

lemma pressureFluctuation_le (A : ι → κ → ℝ) (c : κ → ℝ≥0) (hA : ∀ s k, |A s k|≤c k) :
    pressureFluctuation A ≤ Real.sqrt (∑ k, (c k:ℝ)^2) :=
  logPartition_absolute_fluctuation A c hA

omit [Nonempty ι] in
lemma disorderDeviation_nonneg (A B : ι → κ → ℝ) (t : ℝ) : 0≤disorderDeviation A B t :=
  integral_nonneg fun _ => abs_nonneg _

 

theorem disorderDeviation_le (A B : ι → κ → ℝ) (t : ℝ) {δ : ℝ} (hδ : 0<δ) :
    disorderDeviation A B t ≤
      (pressureFluctuation (affineCoeff A B (t+δ))+2*pressureFluctuation (affineCoeff A B t)+
        pressureFluctuation (affineCoeff A B (t-δ)))/δ+
      (meanLine A B (t+δ)-meanLine A B (t-δ)) := by
  have hd (z : κ → ℝ) := convex_derivative_deviation
    (convex_logPartition_line (field A z) (field B z)) (convex_expectedLine A B)
    (fun u => (hasDerivAt_logPartition_line (field A z) (field B z) u).differentiableAt)
    (fun u => (hasDerivAt_expectedLine A B u).differentiableAt) t hδ
  have he (z : κ → ℝ) :
      |gibbsMean 1 (field A z+t • field B z) (field B z)-meanLine A B t| ≤
        (|logPartition (field (affineCoeff A B (t+δ)) z)-expected (affineCoeff A B (t+δ))|+
        2*|logPartition (field (affineCoeff A B t) z)-expected (affineCoeff A B t)|+
        |logPartition (field (affineCoeff A B (t-δ)) z)-expected (affineCoeff A B (t-δ))|)/δ+
        (meanLine A B (t+δ)-meanLine A B (t-δ)) := by
    simpa only [(hasDerivAt_logPartition_line (field A z) (field B z) t).deriv,
      (hasDerivAt_expectedLine A B t).deriv, (hasDerivAt_expectedLine A B (t+δ)).deriv,
      (hasDerivAt_expectedLine A B (t-δ)).deriv, expectedLine_eq, field_affineCoeff] using hd z
  have hp := integrable_pressureFluctuation (affineCoeff A B (t+δ))
  have hm := integrable_pressureFluctuation (affineCoeff A B (t-δ))
  have h0 := integrable_pressureFluctuation (affineCoeff A B t)
  have hleft := ((integrable_lineMean A B t).sub (integrable_const (meanLine A B t))).abs
  have hright := (((hp.add (h0.const_mul 2)).add hm).div_const δ).add
    (integrable_const (meanLine A B (t+δ)-meanLine A B (t-δ)))
  have h := integral_mono hleft hright he
  simp only [Pi.add_apply] at h
  have hsum : ∫ z, (|logPartition (field (affineCoeff A B (t+δ)) z)-expected (affineCoeff A B (t+δ))|+
        2*|logPartition (field (affineCoeff A B t) z)-expected (affineCoeff A B t)|+
        |logPartition (field (affineCoeff A B (t-δ)) z)-expected (affineCoeff A B (t-δ))|)/δ+
        (meanLine A B (t+δ)-meanLine A B (t-δ)) ∂gaussianLaw κ =
      (pressureFluctuation (affineCoeff A B (t+δ))+2*pressureFluctuation (affineCoeff A B t)+
        pressureFluctuation (affineCoeff A B (t-δ)))/δ+
      (meanLine A B (t+δ)-meanLine A B (t-δ)) := by
    have hh := integral_add (((hp.add (h0.const_mul 2)).add hm).div_const δ) (integrable_const
      (meanLine A B (t+δ)-meanLine A B (t-δ)))
    simp only [Pi.add_apply, integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    rw [hh]
    congr 2
    have hhh := integral_add (hp.add (h0.const_mul 2)) hm
    simp only [Pi.add_apply] at hhh
    rw [hhh, integral_add hp (h0.const_mul 2), integral_const_mul]
    rfl
  rw [hsum] at h
  exact h

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiInterpolation ParisiFinite
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

lemma continuous_meanLine (A B : ι → κ → ℝ) : Continuous (meanLine A B) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_meanLine A B t).continuousAt

lemma continuous_varianceLine (A B : ι → κ → ℝ) : Continuous (varianceLine A B) := by
  apply continuous_of_dominated (bound:=fun z => 2*‖field B z‖^2)
    (fun t => (continuous_lineVariance A B t).aestronglyMeasurable)
    (fun t => ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs, sq, mul_assoc] using
        abs_gibbsCov_le 1 (field A z+t • field B z) (field B z) (field B z))
    ((integrable_norm_field_sq B).const_mul 2)
  exact ae_of_all _ fun z => (continuous_gibbsCov 1 (field B z) (field B z)).comp
    (continuous_const.add (continuous_id.smul continuous_const))

lemma integral_meanLine (A B : ι → κ → ℝ) (a b : ℝ) :
    (∫ t in a..b, meanLine A B t)=expectedLine A B b-expectedLine A B a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_expectedLine A B t)
    ((continuous_meanLine A B).intervalIntegrable a b)

lemma integral_varianceLine (A B : ι → κ → ℝ) (a b : ℝ) :
    (∫ t in a..b, varianceLine A B t)=meanLine A B b-meanLine A B a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_meanLine A B t)
    ((continuous_varianceLine A B).intervalIntegrable a b)

 

lemma integral_meanLine_increment_le (A B : ι → κ → ℝ) (a b : ℝ) {δ : ℝ} (hδ : 0<δ) :
    (∫ t in a..b, (meanLine A B (t+δ)-meanLine A B (t-δ))) ≤
      2*δ*(meanLine A B (b+δ)-meanLine A B (a-δ)) := by
  have hp : Continuous (fun t => meanLine A B (t+δ)) :=
    (continuous_meanLine A B).comp (continuous_id.add_const δ)
  have hm : Continuous (fun t => meanLine A B (t-δ)) :=
    (continuous_meanLine A B).comp (continuous_id.sub continuous_const)
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable a b) (hm.intervalIntegrable a b),
    intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_sub_right,
    integral_meanLine, integral_meanLine]
  have hb := (convex_expectedLine A B).slope_le_deriv (Set.mem_univ (b-δ))
    (Set.mem_univ (b+δ)) (by linarith) (hasDerivAt_expectedLine A B (b+δ)).differentiableAt
  have ha := (convex_expectedLine A B).deriv_le_slope (Set.mem_univ (a-δ))
    (Set.mem_univ (a+δ)) (by linarith) (hasDerivAt_expectedLine A B (a-δ)).differentiableAt
  rw [(hasDerivAt_expectedLine A B (b+δ)).deriv] at hb
  rw [(hasDerivAt_expectedLine A B (a-δ)).deriv] at ha
  simp only [slope_def_field, show b+δ-(b-δ)=2*δ by ring,
    show a+δ-(a-δ)=2*δ by ring] at hb ha
  have hb' := (div_le_iff₀ (by positivity : 0<2*δ)).mp hb
  have ha' := (le_div_iff₀ (by positivity : 0<2*δ)).mp ha
  nlinarith

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiInterpolation ParisiFinite
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

omit [Nonempty ι] in
lemma meanLine_eq_energyMean (A B : ι → κ → ℝ) (t : ℝ) :
    meanLine A B t=energyMean (affineCoeff A B t) B := by
  simp only [meanLine, energyMean, gibbsMean, one_mul, field_affineCoeff]

lemma energyDeviation_amplitude_bound (A B : ι → κ → ℝ) {a b δ V t : ℝ}
    (hδ : 0<δ) (ht : t∈Set.Icc a b)
    (hV : ∀ u∈Set.Icc (a-δ) (b+δ), pressureFluctuation (affineCoeff A B u)≤V) :
    energyDeviation (affineCoeff A B t) B (energyMean (affineCoeff A B t) B) ≤
      varianceLine A B t+(1+4*V/δ)+(meanLine A B (t+δ)-meanLine A B (t-δ)) := by
  have h1 := energyDeviation_le_thermal_add A B t (meanLine A B t)
  change energyDeviation _ _ _ ≤ Real.sqrt (varianceLine A B t)+disorderDeviation A B t at h1
  rw [meanLine_eq_energyMean] at h1
  have h2 := disorderDeviation_le A B t hδ
  have hp := hV (t+δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hm := hV (t-δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0 := hV t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h3 : (pressureFluctuation (affineCoeff A B (t+δ))+2*pressureFluctuation (affineCoeff A B t)+
        pressureFluctuation (affineCoeff A B (t-δ)))/δ ≤ 4*V/δ := by
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hs : Real.sqrt (varianceLine A B t)≤varianceLine A B t+1 := by
    have hh := Real.sq_sqrt (varianceLine_nonneg A B t)
    nlinarith [sq_nonneg (Real.sqrt (varianceLine A B t)-1)]
  linarith

 

theorem exists_amplitude_energyDeviation (A B : ι → κ → ℝ) {a b δ V : ℝ}
    (hab : a<b) (hδ : 0<δ)
    (hV : ∀ u∈Set.Icc (a-δ) (b+δ), pressureFluctuation (affineCoeff A B u)≤V) :
    ∃ t∈Set.Icc a b,
      (b-a)*energyDeviation (affineCoeff A B t) B (energyMean (affineCoeff A B t) B) ≤
        meanLine A B b-meanLine A B a+(b-a)*(1+4*V/δ)+
        2*δ*(meanLine A B (b+δ)-meanLine A B (a-δ)) := by
  let S : ℝ → ℝ := fun t => varianceLine A B t+(1+4*V/δ)+
    (meanLine A B (t+δ)-meanLine A B (t-δ))
  have hc : Continuous S := (continuous_varianceLine A B).add continuous_const |>.add
    (((continuous_meanLine A B).comp (continuous_id.add_const δ)).sub
      ((continuous_meanLine A B).comp (continuous_id.sub continuous_const)))
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab.le) hc.continuousOn
  refine ⟨t, ht, ?_⟩
  have hlow := intervalIntegral.integral_mono_on (μ:=volume) hab.le
    (continuous_const.intervalIntegrable a b) (hc.intervalIntegrable a b) (fun u hu => hmin hu)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have hp : Continuous (fun t => meanLine A B (t+δ)-meanLine A B (t-δ)) :=
    ((continuous_meanLine A B).comp (continuous_id.add_const δ)).sub
      ((continuous_meanLine A B).comp (continuous_id.sub continuous_const))
  have he : (∫ u in a..b, S u) = meanLine A B b-meanLine A B a+(b-a)*(1+4*V/δ)+
      ∫ u in a..b, (meanLine A B (u+δ)-meanLine A B (u-δ)) := by
    change (∫ u in a..b, (varianceLine A B u+(1+4*V/δ))+
      (meanLine A B (u+δ)-meanLine A B (u-δ))) = _
    have hi : IntervalIntegrable (fun u => varianceLine A B u+(1+4*V/δ)) volume a b :=
      ((continuous_varianceLine A B).add continuous_const).intervalIntegrable a b
    rw [intervalIntegral.integral_add hi (hp.intervalIntegrable a b)]
    rw [intervalIntegral.integral_add ((continuous_varianceLine A B).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), integral_varianceLine, intervalIntegral.integral_const, smul_eq_mul]
  have hu := integral_meanLine_increment_le A B a b hδ
  have hh := mul_le_mul_of_nonneg_left (energyDeviation_amplitude_bound A B hδ ht hV) (sub_nonneg.mpr hab.le)
  change (b-a)*energyDeviation _ _ _≤(b-a)*S t at hh
  rw [he] at hlow
  linarith

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite GaussianConcentration

lemma affineCoeff_perturbed (n p : ℕ) (β t : ℝ) :
    affineCoeff (perturbedCoeff n p β 0) (perturbationNoise n p) t=perturbedCoeff n p β t := by
  funext σ k
  cases k <;> simp [affineCoeff, perturbedCoeff, perturbationNoise]

lemma pSpin_meanLine (n p : ℕ) (β t : ℝ) :
    meanLine (perturbedCoeff n p β 0) (perturbationNoise n p) t=
      energyMean (perturbedCoeff n p β t) (perturbationNoise n p) := by
  rw [meanLine_eq_energyMean, affineCoeff_perturbed]

lemma pSpin_energyMean_bounds {n : ℕ} (hn : 0<n) (p : ℕ) (β : ℝ) {t : ℝ} (ht : 0≤t) :
    0≤energyMean (perturbedCoeff n p β t) (perturbationNoise n p) ∧
      energyMean (perturbedCoeff n p β t) (perturbationNoise n p)≤2*t := by
  have hb : |averagedReplica (perturbedCoeff n p β t)
      (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^p)|≤1 := by
    apply averagedReplica_abs_bound
    intro τ
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_overlap_le_one _ _)
  rw [pSpin_energyMean hn]
  rw [abs_le] at hb
  constructor
  · exact mul_nonneg ht (by linarith)
  · nlinarith [mul_le_mul_of_nonneg_left hb.1 ht]

lemma pSpin_pressureFluctuation_le {n : ℕ} (hn : 0<n) (p : ℕ) (β t : ℝ) :
    pressureFluctuation (perturbedCoeff n p β t)≤Real.sqrt (β^2*((n:ℝ)-1)/2+t^2) := by
  exact (integral_abs_centered_le_sqrt_variance (memLp_logPartition_field _)).trans
    (Real.sqrt_le_sqrt (perturbed_logPartition_variance_le hn p β t))

 

theorem exists_pSpin_energy_amplitude {n : ℕ} (hn : 0<n) (p : ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) :
    ∃ t∈Set.Icc s (2*s),
      energyDeviation (perturbedCoeff n p β t) (perturbationNoise n p)
        (energyMean (perturbedCoeff n p β t) (perturbationNoise n p)) ≤
      5+4*Real.sqrt (β^2*(n:ℝ)/2+9*s^2)/δ+12*δ := by
  let A := perturbedCoeff n p β 0
  let B := perturbationNoise n p
  let V := Real.sqrt (β^2*(n:ℝ)/2+9*s^2)
  have hV (u : ℝ) (hu : u∈Set.Icc (s-δ) (2*s+δ)) :
      pressureFluctuation (affineCoeff A B u)≤V := by
    dsimp [A, B]
    rw [affineCoeff_perturbed]
    apply (pSpin_pressureFluctuation_le hn p β u).trans
    apply Real.sqrt_le_sqrt
    have hu0 : 0≤u := by linarith [hu.1]
    have hu3 : u≤3*s := by linarith [hu.2]
    have hu2 : u^2≤9*s^2 := by nlinarith [sq_nonneg (3*s-u)]
    nlinarith [sq_nonneg β]
  obtain ⟨t, ht, h⟩ := exists_amplitude_energyDeviation A B (show s<2*s by linarith) hδ hV
  simp only [A, B, affineCoeff_perturbed, pSpin_meanLine, show 2*s-s=s by ring] at h
  refine ⟨t, ht, ?_⟩
  have h2 := pSpin_energyMean_bounds hn p β (t:=2*s) (by linarith)
  have h1 := pSpin_energyMean_bounds hn p β hs.le
  have hup := pSpin_energyMean_bounds hn p β (t:=2*s+δ) (by linarith)
  have hlo := pSpin_energyMean_bounds hn p β (t:=s-δ) (by linarith)
  have hd : 2*δ*(energyMean (perturbedCoeff n p β (2*s+δ)) (perturbationNoise n p)-
      energyMean (perturbedCoeff n p β (s-δ)) (perturbationNoise n p)) ≤12*δ*s := by
    have hh : energyMean (perturbedCoeff n p β (2*s+δ)) (perturbationNoise n p)-
        energyMean (perturbedCoeff n p β (s-δ)) (perturbationNoise n p) ≤6*s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤2*δ)]
  have hb : s*energyDeviation (perturbedCoeff n p β t) (perturbationNoise n p)
      (energyMean (perturbedCoeff n p β t) (perturbationNoise n p)) ≤
      s*(5+4*V/δ+12*δ) := by nlinarith
  nlinarith only [hb, hs]

 

theorem exists_pSpin_GG_amplitude {n : ℕ} (hn : 0<n) (p : ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) :
    ∃ t∈Set.Icc s (2*s), ∀ (r : ℕ) (i : Fin r)
      (f : (Fin r → Configuration n) → ℝ), (∀ σ, |f σ|≤1) →
      |pSpinGGDefect p β t i f|≤(5+4*Real.sqrt (β^2*(n:ℝ)/2+9*s^2)/δ+12*δ)/s := by
  obtain ⟨t, ht, h⟩ := exists_pSpin_energy_amplitude hn p β hs hδ hδs
  refine ⟨t, ht, fun r i f hf => ?_⟩
  have hgg := pSpinGGDefect_bound hn p β t i f (by norm_num : (0:ℝ)≤1) hf
  rw [one_mul, abs_mul, abs_of_nonneg (le_trans hs.le ht.1)] at hgg
  have ha := mul_le_mul_of_nonneg_right ht.1 (abs_nonneg (pSpinGGDefect p β t i f))
  apply (le_div_iff₀ hs).mpr
  nlinarith only [ha, hgg, h]

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

def eighthRootScale (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (n:ℝ)))

lemma eighthRootScale_nonneg (n : ℕ) : 0≤eighthRootScale n := Real.sqrt_nonneg _

lemma eighthRootScale_pow_eight (n : ℕ) : (eighthRootScale n)^8=(n:ℝ) := by
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt (n:ℝ)))
  have h2 := Real.sq_sqrt (Real.sqrt_nonneg (n:ℝ))
  have h3 := Real.sq_sqrt (Nat.cast_nonneg n)
  change eighthRootScale n^2=Real.sqrt (Real.sqrt (n:ℝ)) at h1
  calc
    eighthRootScale n^8=(eighthRootScale n^2)^4 := by ring
    _=(Real.sqrt (Real.sqrt (n:ℝ))^2)^2 := by rw [h1]; ring
    _=(n:ℝ) := by rw [h2, h3]

lemma one_le_eighthRootScale {n : ℕ} (hn : 0<n) : 1≤eighthRootScale n := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have h1 := Real.sqrt_le_sqrt hn'
  have h2 := Real.sqrt_le_sqrt h1
  have h3 := Real.sqrt_le_sqrt h2
  simpa only [Real.sqrt_one, eighthRootScale] using h3

lemma tendsto_eighthRootScale : Tendsto eighthRootScale atTop atTop :=
  Real.tendsto_sqrt_atTop.comp <| Real.tendsto_sqrt_atTop.comp <|
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

lemma eighthRoot_pressure_scale_bound {n : ℕ} (hn : 0<n) (β : ℝ) :
    Real.sqrt (β^2*(n:ℝ)/2+9*(eighthRootScale n^3)^2) ≤
      (|β|+3)*eighthRootScale n^4 := by
  let r := eighthRootScale n
  have hr : 1≤r := one_le_eighthRootScale hn
  have hr0 : 0≤r := by linarith
  have hc : 0≤|β|+3 := by positivity
  have hp : (r^3)^2≤r^8 := by
    have h : r^6≤r^8 := pow_le_pow_right₀ hr (by norm_num : 6≤8)
    nlinarith only [h]
  have hn' : (n:ℝ)=r^8 := (eighthRootScale_pow_eight n).symm
  have hβ : β^2/2+9≤(|β|+3)^2 := by nlinarith [sq_abs β, abs_nonneg β, sq_nonneg β]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · change β^2*(n:ℝ)/2+9*(r^3)^2 ≤ ((|β|+3)*r^4)^2
    rw [hn']
    have hh := mul_le_mul_of_nonneg_right hβ (pow_nonneg hr0 8)
    nlinarith only [hh, hp]

lemma eighthRoot_GG_bound {n : ℕ} (hn : 0<n) (β : ℝ) :
    (5+4*Real.sqrt (β^2*(n:ℝ)/2+9*(eighthRootScale n^3)^2)/(eighthRootScale n^2)+
      12*(eighthRootScale n^2))/(eighthRootScale n^3) ≤
      (29+4*|β|)/eighthRootScale n := by
  let r := eighthRootScale n
  have hr : 1≤r := one_le_eighthRootScale hn
  have hrp : 0<r := by linarith
  have hb := eighthRoot_pressure_scale_bound hn β
  change Real.sqrt (β^2*(n:ℝ)/2+9*(r^3)^2) ≤ (|β|+3)*r^4 at hb
  have hb' := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)
  have hd := div_le_div_of_nonneg_right hb' (sq_nonneg r)
  have he : 4*((|β|+3)*r^4)/r^2=4*(|β|+3)*r^2 := by field_simp
  rw [he] at hd
  change (5+4*Real.sqrt (β^2*(n:ℝ)/2+9*(r^3)^2)/r^2+12*r^2)/r^3 ≤ (29+4*|β|)/r
  apply (div_le_iff₀ (pow_pos hrp 3)).mpr
  have he' : ((29+4*|β|)/r)*r^3=(29+4*|β|)*r^2 := by field_simp
  rw [he']
  nlinarith [sq_nonneg (r-1)]

lemma eighthRoot_amplitude_pressure_bound {n : ℕ} (hn : 0<n) {t : ℝ}
    (ht : t∈Set.Icc (eighthRootScale n^3) (2*eighthRootScale n^3)) :
    t^2/(n:ℝ)≤4/(eighthRootScale n^2) := by
  let r := eighthRootScale n
  have hr : 0<r := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_eighthRootScale hn)
  have ht0 : 0≤t := le_trans (by positivity : (0:ℝ)≤r^3) ht.1
  have ht2 : t^2≤4*r^6 := by nlinarith [ht.2]
  have hn' : (n:ℝ)=r^8 := (eighthRootScale_pow_eight n).symm
  change t^2/(n:ℝ)≤4/r^2
  rw [hn']
  have he : 4/r^2=(4*r^6)/r^8 := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_right ht2 (pow_nonneg hr.le 8)

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma exists_rootScale_GG_amplitude {n : ℕ} (hn : 0<n) (p : ℕ) (β : ℝ) :
    ∃ t∈Set.Icc (eighthRootScale n^3) (2*eighthRootScale n^3),
      ∀ (r : ℕ) (i : Fin r) (f : (Fin r → Configuration n) → ℝ),
        (∀ σ, |f σ|≤1) → |pSpinGGDefect p β t i f|≤(29+4*|β|)/eighthRootScale n := by
  have hh := one_le_eighthRootScale hn
  have hp : 0<eighthRootScale n := by linarith
  have hδs : eighthRootScale n^2≤eighthRootScale n^3 := pow_le_pow_right₀ hh (by norm_num : 2≤3)
  obtain ⟨t, ht, h⟩ := exists_pSpin_GG_amplitude hn p β (pow_pos hp 3) (pow_pos hp 2) hδs
  exact ⟨t, ht, fun r i f hf => (h r i f hf).trans (eighthRoot_GG_bound hn β)⟩

 

def genericPSpinAmplitude (n p : ℕ) (β : ℝ) : ℝ :=
  if hn : 0<n then (exists_rootScale_GG_amplitude hn p β).choose else 0

lemma genericPSpinAmplitude_mem {n : ℕ} (hn : 0<n) (p : ℕ) (β : ℝ) :
    genericPSpinAmplitude n p β∈Set.Icc (eighthRootScale n^3) (2*eighthRootScale n^3) := by
  rw [genericPSpinAmplitude, dite_eq_left hn]
  exact (exists_rootScale_GG_amplitude hn p β).choose_spec.1

lemma genericPSpinAmplitude_defect_le {n : ℕ} (hn : 0<n) (p : ℕ) (β : ℝ)
    {r : ℕ} (i : Fin r) (f : (Fin r → Configuration n) → ℝ) (hf : ∀ σ, |f σ|≤1) :
    |pSpinGGDefect p β (genericPSpinAmplitude n p β) i f|≤(29+4*|β|)/eighthRootScale n := by
  rw [genericPSpinAmplitude, dite_eq_left hn]
  exact (exists_rootScale_GG_amplitude hn p β).choose_spec.2 r i f hf

 

theorem tendsto_genericPSpin_GG_defect (p : ℕ → ℕ) (β : ℝ) (r : ℕ → ℕ)
    (i : ∀ n, Fin (r n)) (f : ∀ n, (Fin (r n) → Configuration n) → ℝ)
    (hf : ∀ n σ, |f n σ|≤1) :
    Tendsto (fun n => pSpinGGDefect (p n) β (genericPSpinAmplitude n (p n) β) (i n) (f n))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  refine squeeze_zero' (g:=fun n => (29+4*|β|)/eighthRootScale n) (Eventually.of_forall fun n => abs_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact genericPSpinAmplitude_defect_le hn (p n) β (i n) (f n) (hf n)
  · have h := (tendsto_inv_atTop_zero.comp tendsto_eighthRootScale).const_mul (29+4*|β|)
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using h

lemma tendsto_genericPSpin_amplitude_squared_density (p : ℕ → ℕ) (β : ℝ) :
    Tendsto (fun n => (genericPSpinAmplitude n (p n) β)^2/(n:ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => (eighthRootScale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_eighthRootScale
  have hlim : Tendsto (fun n => 4/(eighthRootScale n^2)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2≠0), mul_zero, inv_pow, div_eq_mul_inv] using (hr.pow 2).const_mul 4
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact eighthRoot_amplitude_pressure_bound hn (genericPSpinAmplitude_mem hn (p n) β)

 

theorem tendsto_genericPSpin_pressureDensity_error (p : ℕ → ℕ) (β : ℝ) :
    Tendsto (fun n => (expected (perturbedCoeff n (p n) β (genericPSpinAmplitude n (p n) β))-
      expected (fun s e => β*skCoeff n s e))/(n:ℝ)) atTop (𝓝 0) :=
  tendsto_perturbed_pressureDensity_error p β _ (tendsto_genericPSpin_amplitude_squared_density p β)

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev MixedIndex (n : ℕ) (d : K → ℕ) := Edge n ⊕ (Σ k : K, Fin (d k) → Fin n)

 

def mixedCoeff (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (σ : Configuration n) :
    MixedIndex n d → ℝ :=
  Sum.elim (fun e => β*skCoeff n σ e) (fun u => x u.1*pSpinCoeff n (d u.1) σ u.2)

 
def mixedNoise (n : ℕ) (d : K → ℕ) (k : K) (σ : Configuration n) : MixedIndex n d → ℝ :=
  Sum.elim (fun _ => 0) (fun u => if u.1=k then pSpinCoeff n (d u.1) σ u.2 else 0)

omit [DecidableEq K] in
lemma mixedCoeff_kernel {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration n) :
    kernel (mixedCoeff n d β x) σ τ =
      β^2*((overlapSum σ τ)^2-(n:ℝ))/(2*n)+∑ k, (x k)^2*(overlap σ τ)^(d k) := by
  unfold kernel mixedCoeff
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sigma]
  change kernel (fun s e => β*skCoeff n s e) σ τ+
    (∑ k, kernel (fun s u => x k*pSpinCoeff n (d k) s u) σ τ)=_
  simp_rw [kernel_scale, pSpinCoeff_kernel hn]
  rw [kernel, coeff_covariance hn]
  ring

lemma mixedNoise_crossCov {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (k : K) (σ τ : Configuration n) :
    crossCov (mixedNoise n d k) (mixedCoeff n d β x) σ τ = x k*(overlap σ τ)^(d k) := by
  unfold crossCov mixedNoise mixedCoeff
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, zero_add, Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
    calc
      (∑ u, pSpinCoeff n (d k) σ u*(x k*pSpinCoeff n (d k) τ u)) =
          x k*kernel (pSpinCoeff n (d k)) σ τ := by
        simp only [kernel, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by rw [pSpinCoeff_kernel hn]
  · intro j _ hj
    simp only [hj, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

omit [Fintype K] [DecidableEq K] in
lemma mixedCoeff_abs (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration n) (a : MixedIndex n d) :
    |mixedCoeff n d β x σ a|=|mixedCoeff n d β x τ a| := by
  cases a with
  | inl e => simp [mixedCoeff, skCoeff, abs_mul, spin_abs]
  | inr u => simp [mixedCoeff, abs_mul, pSpinCoeff_abs]

omit [DecidableEq K] in
lemma mixedCoeff_diag {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ : Configuration n) :
    kernel (mixedCoeff n d β x) σ σ=β^2*((n:ℝ)-1)/2+∑ k, (x k)^2 := by
  rw [mixedCoeff_kernel hn, overlap_self hn]
  simp only [one_pow, mul_one]
  have hs : overlapSum σ σ=(n:ℝ) := by simp [overlapSum, ← sq, spin_sq]
  rw [hs]
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

omit [DecidableEq K] in
lemma mixed_pressureFluctuation_le {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    pressureFluctuation (mixedCoeff n d β x) ≤ Real.sqrt (β^2*((n:ℝ)-1)/2+∑ k, (x k)^2) := by
  have hv := variance_logPartition_le_diagonal (mixedCoeff n d β x) (fun _ => false)
    (fun τ a => mixedCoeff_abs n d β x τ (fun _ => false) a)
  rw [mixedCoeff_diag hn] at hv
  exact (GaussianConcentration.integral_abs_centered_le_sqrt_variance
    (GaussianConcentration.memLp_logPartition_field _)).trans (Real.sqrt_le_sqrt hv)

omit [Fintype K] in
lemma affineCoeff_mixed_update (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K) (t : ℝ) :
    affineCoeff (mixedCoeff n d β (Function.update x k 0)) (mixedNoise n d k) t=
      mixedCoeff n d β (Function.update x k t) := by
  funext σ a
  cases a with
  | inl e => simp [affineCoeff, mixedCoeff, mixedNoise]
  | inr u =>
    by_cases h : u.1=k
    · subst k
      simp [affineCoeff, mixedCoeff, mixedNoise]
    · simp [affineCoeff, mixedCoeff, mixedNoise, h]

end SKCavity

end

end OAI
