import Mathlib
import OAI.Probability.ParisiFinite.VarianceProdDecomposition

namespace OAI

/-! Increment Eq Kernel. -/

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
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma increment_eq_kernel {ι κ : Type*} [Fintype κ] (A : ι → κ → ℝ) (s t : ι) :
    ParisiInterpolation.increment A s t = kernel A s s+kernel A t t-2*kernel A s t := by
  simp only [ParisiInterpolation.increment, kernel, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma increment_perturbed_sub {n : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ)
    (σ τ : Configuration n) :
    ParisiInterpolation.increment (perturbedCoeff n p β a) σ τ-
      ParisiInterpolation.increment (fun s e => β*skCoeff n s e) σ τ =
      2*a^2*(1-(overlap σ τ)^p) := by
  have hk (s t : Configuration n) : kernel (perturbedCoeff n p β a) s t =
      kernel (fun s e => β*skCoeff n s e) s t+a^2*(overlap s t)^p := by
    rw [perturbedCoeff_kernel hn, kernel_scale, kernel, coeff_covariance hn]
    ring
  rw [increment_eq_kernel, increment_eq_kernel, hk, hk, hk,
    overlap_self hn, overlap_self hn, one_pow]
  ring

lemma abs_increment_perturbed_sub_le {n : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ)
    (σ τ : Configuration n) :
    |ParisiInterpolation.increment (perturbedCoeff n p β a) σ τ-
      ParisiInterpolation.increment (fun s e => β*skCoeff n s e) σ τ| ≤ 4*a^2 := by
  rw [increment_perturbed_sub hn, abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤2*a^2)]
  have h : |(overlap σ τ)^p| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_overlap_le_one _ _)
  have hd : |1-(overlap σ τ)^p| ≤ 2 := by
    have := abs_sub_le (1:ℝ) 0 ((overlap σ τ)^p)
    simp only [sub_zero, zero_sub, abs_neg, abs_one] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0:ℝ) ≤ 2*a^2)]

 

theorem perturbed_pressure_error {n : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ) :
    |expected (perturbedCoeff n p β a)-expected (fun s e => β*skCoeff n s e)| ≤
      Real.pi*a^2 := by
  have h := expected_difference_le (fun s e => β*skCoeff n s e) (perturbedCoeff n p β a)
    (show (0:ℝ)≤4*a^2 by positivity) (abs_increment_perturbed_sub_le hn p β a)
  convert h using 1
  ring

 

theorem tendsto_perturbed_pressureDensity_error (p : ℕ → ℕ) (β : ℝ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n => (a n)^2/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (expected (perturbedCoeff n (p n) β (a n))-
      expected (fun s e => β*skCoeff n s e))/(n:ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have hlim : Tendsto (fun n : ℕ => Real.pi*((a n)^2/(n:ℝ))) atTop (𝓝 0) := by
    simpa using ha.const_mul Real.pi
  refine squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [abs_div, abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
  have h := div_le_div_of_nonneg_right (perturbed_pressure_error hn (p n) β (a n))
    (Nat.cast_nonneg n)
  simpa only [mul_div_assoc] using h

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

def perturbationNoise (n p : ℕ) (σ : Configuration n) :
    Edge n ⊕ (Fin p → Fin n) → ℝ := Sum.elim (fun _ => 0) (pSpinCoeff n p σ)

lemma perturbationNoise_crossCov {n : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ)
    (σ τ : Configuration n) :
    crossCov (perturbationNoise n p) (perturbedCoeff n p β a) σ τ =
      a*(overlap σ τ)^p := by
  simp only [crossCov, perturbationNoise, perturbedCoeff, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add]
  have he (u : Fin p → Fin n) : pSpinCoeff n p σ u*(a*pSpinCoeff n p τ u)=
      a*(pSpinCoeff n p σ u*pSpinCoeff n p τ u) := by ring
  simp_rw [he, ← Finset.mul_sum]
  rw [← kernel, pSpinCoeff_kernel hn]

 

theorem pSpin_replica_identity {n r : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ) :
    (∫ z, ∑ σ, replicaWeight (field (perturbedCoeff n p β a) z) σ*
      (field (perturbationNoise n p) z (σ i)*f σ)
      ∂gaussianLaw (Edge n ⊕ (Fin p → Fin n))) =
      a*(∫ z, replicaMean (field (perturbedCoeff n p β a) z)
        (fun σ => f σ*∑ l, (overlap (σ i) (σ l))^p)
        ∂gaussianLaw (Edge n ⊕ (Fin p → Fin n))) -
      (r:ℝ)*a*(∫ z, replicaMean (field (perturbedCoeff n p β a) z)
        (fun τ : Fin (r+1) → Configuration n =>
          f (fun l => τ l.castSucc)*(overlap (τ i.castSucc) (τ (Fin.last r)))^p)
        ∂gaussianLaw (Edge n ⊕ (Fin p → Fin n))) := by
  have h := integral_field_replica_energy_covariance
    (perturbedCoeff n p β a) (perturbationNoise n p) i f
  simp_rw [perturbationNoise_crossCov hn] at h
  simp only [replicaMean, ← Finset.mul_sum] at h ⊢
  have he₁ (σ : Fin r → Configuration n) (z) :
      replicaWeight (field (perturbedCoeff n p β a) z) σ*
        (f σ*(a*∑ l, overlap (σ i) (σ l)^p)) =
      a*(replicaWeight (field (perturbedCoeff n p β a) z) σ*
        (f σ*∑ l, overlap (σ i) (σ l)^p)) := by ring
  have he₂ (τ : Fin (r+1) → Configuration n) (z) :
      replicaWeight (field (perturbedCoeff n p β a) z) τ*
        (f (fun l => τ l.castSucc)*(a*overlap (τ i.castSucc) (τ (Fin.last r))^p)) =
      a*(replicaWeight (field (perturbedCoeff n p β a) z) τ*
        (f (fun l => τ l.castSucc)*overlap (τ i.castSucc) (τ (Fin.last r))^p)) := by ring
  simp_rw [he₁, he₂, ← Finset.mul_sum, integral_const_mul] at h
  convert h using 1
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace ParisiFinite
open SKGaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma gibbsCov_self_nonneg (β : ℝ) (x v : ι → ℝ) : 0 ≤ gibbsCov β x v v := by
  have h := weighted_covariance (weight (fun j => β*x j)) v v (sum_weight _)
  have hs : 0 ≤ ∑ i, ∑ j, weight (fun j => β*x j) i*weight (fun j => β*x j) j*
      (v i-v j)*(v i-v j) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have he : weight (fun j => β*x j) i*weight (fun j => β*x j) j*
        (v i-v j)*(v i-v j) =
        (weight (fun j => β*x j) i*weight (fun j => β*x j) j)*(v i-v j)^2 := by ring
    rw [he]
    exact mul_nonneg (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le) (sq_nonneg _)
  rw [h] at hs
  unfold gibbsCov gibbsMean
  simp only [mul_assoc] at hs
  linarith

 
lemma monotone_gibbsMean_line (x v : ι → ℝ) :
    Monotone (fun t : ℝ => gibbsMean 1 (x+t • v) v) := by
  apply monotone_of_hasDerivAt_nonneg (fun t => hasDerivAt_gibbsMean 1 v v x t)
  intro t
  change (0:ℝ) ≤ 1*gibbsCov 1 (x+t • v) v v
  simpa only [one_mul] using gibbsCov_self_nonneg 1 (x+t • v) v

lemma hasDerivAt_logPartition_line (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => logPartition (x+u • v)) (gibbsMean 1 (x+t • v) v) t := by
  simpa only [spinTrace, one_mul, div_one] using hasDerivAt_spinTrace (by norm_num : (1:ℝ) ≠ 0) v x t

lemma convex_logPartition_line (x v : ι → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => logPartition (x+t • v)) := by
  have hd : deriv (fun t : ℝ => logPartition (x+t • v)) = fun t => gibbsMean 1 (x+t • v) v := by
    funext t
    exact (hasDerivAt_logPartition_line x v t).deriv
  apply Monotone.convexOn_univ_of_deriv (fun t => (hasDerivAt_logPartition_line x v t).differentiableAt)
  rw [hd]
  exact monotone_gibbsMean_line x v

 

theorem convex_derivative_deviation {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g)
    (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (x : ℝ) {δ : ℝ} (hδ : 0<δ) :
    |deriv f x-deriv g x| ≤
      (|f (x+δ)-g (x+δ)|+2*|f x-g x|+|f (x-δ)-g (x-δ)|)/δ+
      (deriv g (x+δ)-deriv g (x-δ)) := by
  have hfL := hf.slope_le_deriv (Set.mem_univ (x-δ)) (Set.mem_univ x) (by linarith) (hfd x)
  have hfR := hf.deriv_le_slope (Set.mem_univ x) (Set.mem_univ (x+δ)) (by linarith) (hfd x)
  have hgL := hg.deriv_le_slope (Set.mem_univ (x-δ)) (Set.mem_univ x) (by linarith) (hgd (x-δ))
  have hgR := hg.slope_le_deriv (Set.mem_univ x) (Set.mem_univ (x+δ)) (by linarith) (hgd (x+δ))
  have hm := hg.monotoneOn_deriv (fun x _ => hgd x)
  have hmgL := hm (Set.mem_univ (x-δ)) (Set.mem_univ x) (by linarith)
  have hmgR := hm (Set.mem_univ x) (Set.mem_univ (x+δ)) (by linarith)
  simp only [slope_def_field, show x-(x-δ)=δ by ring, show x+δ-x=δ by ring] at hfL hfR hgL hgR
  have hfL' := (div_le_iff₀ hδ).mp hfL
  have hfR' := (le_div_iff₀ hδ).mp hfR
  have hgL' := (le_div_iff₀ hδ).mp hgL
  have hgR' := (div_le_iff₀ hδ).mp hgR
  have h0 := le_abs_self (f x-g x)
  have h0' := neg_abs_le (f x-g x)
  have hp := le_abs_self (f (x+δ)-g (x+δ))
  have hm' := le_abs_self (f (x-δ)-g (x-δ))
  rw [abs_le]
  constructor
  · have hq : (deriv g x-deriv f x-(deriv g (x+δ)-deriv g (x-δ)))*δ ≤
        |f (x+δ)-g (x+δ)|+2*|f x-g x|+|f (x-δ)-g (x-δ)| := by
      nlinarith [abs_nonneg (f (x+δ)-g (x+δ)), mul_le_mul_of_nonneg_right hmgR hδ.le]
    have h := (le_div_iff₀ hδ).mpr hq
    linarith
  · have hq : (deriv f x-deriv g x-(deriv g (x+δ)-deriv g (x-δ)))*δ ≤
        |f (x+δ)-g (x+δ)|+2*|f x-g x|+|f (x-δ)-g (x-δ)| := by
      nlinarith [abs_nonneg (f (x-δ)-g (x-δ)), mul_le_mul_of_nonneg_right hmgL hδ.le]
    have h := (le_div_iff₀ hδ).mpr hq
    linarith

end ParisiFinite

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

omit [Nonempty ι] in
lemma norm_field_le_sum (B : ι → κ → ℝ) (z : κ → ℝ) :
    ‖field B z‖ ≤ ∑ s, |field B z s| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro s
  simpa only [Real.norm_eq_abs] using Finset.single_le_sum
    (fun t (_ : t ∈ (Finset.univ : Finset ι)) => abs_nonneg (field B z t)) (Finset.mem_univ s)

omit [Nonempty ι] in
lemma integrable_norm_field (B : ι → κ → ℝ) :
    Integrable (fun z => ‖field B z‖) (gaussianLaw κ) := by
  apply (integrable_finsetSum Finset.univ (fun s _ => (integrable_field B s).abs)).mono'
    (continuous_field B).norm.aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_field_le_sum B z

omit [Fintype ι] [Nonempty ι] in
lemma memLp_field_two (B : ι → κ → ℝ) (s : ι) :
    MemLp (fun z => field B z s) 2 (gaussianLaw κ) := by
  unfold field
  apply memLp_finsetSum
  intro k _
  have h : MemLp (fun z : κ → ℝ => z k) 2 (gaussianLaw κ) := by
    exact (memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
      (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)
  exact h.const_mul _

omit [Nonempty ι] in
lemma memLp_norm_field_two (B : ι → κ → ℝ) :
    MemLp (fun z => ‖field B z‖) 2 (gaussianLaw κ) := by
  have h : MemLp (fun z => ∑ s, |field B z s|) 2 (gaussianLaw κ) :=
    memLp_finsetSum Finset.univ (fun s _ => (memLp_field_two B s).norm)
  apply h.mono' (continuous_field B).norm.aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_field_le_sum B z

omit [Nonempty ι] in
lemma integrable_norm_field_sq (B : ι → κ → ℝ) :
    Integrable (fun z => ‖field B z‖^2) (gaussianLaw κ) := by
  exact (memLp_norm_field_two B).integrable_sq

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiFinite ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

def affineCoeff (A B : ι → κ → ℝ) (t : ℝ) (s : ι) (k : κ) : ℝ := A s k+t*B s k

omit [Fintype ι] [Nonempty ι] in
lemma field_affineCoeff (A B : ι → κ → ℝ) (t : ℝ) (z : κ → ℝ) :
    field (affineCoeff A B t) z=field A z+t • field B z := by
  ext s
  simp only [field, affineCoeff, add_mul, Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

def expectedLine (A B : ι → κ → ℝ) (t : ℝ) : ℝ :=
  ∫ z, logPartition (field A z+t • field B z) ∂gaussianLaw κ

def meanLine (A B : ι → κ → ℝ) (t : ℝ) : ℝ :=
  ∫ z, gibbsMean 1 (field A z+t • field B z) (field B z) ∂gaussianLaw κ

def varianceLine (A B : ι → κ → ℝ) (t : ℝ) : ℝ :=
  ∫ z, gibbsCov 1 (field A z+t • field B z) (field B z) (field B z) ∂gaussianLaw κ

omit [Nonempty ι] in
lemma expectedLine_eq (A B : ι → κ → ℝ) (t : ℝ) :
    expectedLine A B t=expected (affineCoeff A B t) := by
  simp [expectedLine, expected, field_affineCoeff]

lemma continuous_lineMean (A B : ι → κ → ℝ) (t : ℝ) :
    Continuous (fun z => gibbsMean 1 (field A z+t • field B z) (field B z)) := by
  unfold gibbsMean
  apply continuous_finsetSum
  intro s _
  apply Continuous.mul
  · have hc : Continuous (fun z => field A z+t • field B z) :=
      (continuous_field A).add ((continuous_field B).const_smul t)
    simp only [one_mul]
    change Continuous (fun z => weight (field A z+t • field B z) s)
    exact (continuous_weight s).comp hc
  · exact (continuous_apply s).comp (continuous_field B)

lemma continuous_lineVariance (A B : ι → κ → ℝ) (t : ℝ) :
    Continuous (fun z => gibbsCov 1 (field A z+t • field B z) (field B z) (field B z)) := by
  unfold gibbsCov
  apply Continuous.sub
  · unfold gibbsMean
    apply continuous_finsetSum
    intro s _
    apply Continuous.mul
    · have hc : Continuous (fun z => field A z+t • field B z) :=
        (continuous_field A).add ((continuous_field B).const_smul t)
      simp only [one_mul]
      change Continuous (fun z => weight (field A z+t • field B z) s)
      exact (continuous_weight s).comp hc
    · exact ((continuous_apply s).comp (continuous_field B)).mul
        ((continuous_apply s).comp (continuous_field B))
  · exact (continuous_lineMean A B t).mul (continuous_lineMean A B t)

lemma integrable_lineMean (A B : ι → κ → ℝ) (t : ℝ) :
    Integrable (fun z => gibbsMean 1 (field A z+t • field B z) (field B z)) (gaussianLaw κ) := by
  apply (integrable_norm_field B).mono' (continuous_lineMean A B t).aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using abs_gibbsMean_le 1 (field A z+t • field B z) (field B z)

lemma integrable_lineVariance (A B : ι → κ → ℝ) (t : ℝ) :
    Integrable (fun z => gibbsCov 1 (field A z+t • field B z) (field B z) (field B z)) (gaussianLaw κ) := by
  apply ((integrable_norm_field_sq B).const_mul 2).mono'
    (continuous_lineVariance A B t).aestronglyMeasurable
  filter_upwards with z
  have h := abs_gibbsCov_le 1 (field A z+t • field B z) (field B z) (field B z)
  simpa only [Real.norm_eq_abs, sq, mul_assoc] using h

 

theorem hasDerivAt_expectedLine (A B : ι → κ → ℝ) (t₀ : ℝ) :
    HasDerivAt (expectedLine A B) (meanLine A B t₀) t₀ := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Set.univ) (bound:=fun z => ‖field B z‖)
    (F':=fun t z => gibbsMean 1 (field A z+t • field B z) (field B z))
    (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_norm_field B) ?_).2
  · exact Eventually.of_forall fun t => (continuous_logPartition.comp
      ((continuous_field A).add ((continuous_field B).const_smul t))).aestronglyMeasurable
  · exact integrable_logPartition (fun s => (integrable_field A s).add ((integrable_field B s).const_mul t₀))
  · exact (continuous_lineMean A B t₀).aestronglyMeasurable
  · exact ae_of_all _ fun z t _ => by
      simpa only [Real.norm_eq_abs] using abs_gibbsMean_le 1 (field A z+t • field B z) (field B z)
  · exact ae_of_all _ fun z t _ => hasDerivAt_logPartition_line (field A z) (field B z) t

 
theorem hasDerivAt_meanLine (A B : ι → κ → ℝ) (t₀ : ℝ) :
    HasDerivAt (meanLine A B) (varianceLine A B t₀) t₀ := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Set.univ) (bound:=fun z => 2*‖field B z‖^2)
    (F':=fun t z => gibbsCov 1 (field A z+t • field B z) (field B z) (field B z))
    (Filter.univ_mem) ?_ (integrable_lineMean A B t₀) ?_ ?_
    ((integrable_norm_field_sq B).const_mul 2) ?_).2
  · exact Eventually.of_forall fun t => (continuous_lineMean A B t).aestronglyMeasurable
  · exact (continuous_lineVariance A B t₀).aestronglyMeasurable
  · exact ae_of_all _ fun z t _ => by
      simpa only [Real.norm_eq_abs, sq, mul_assoc] using
        abs_gibbsCov_le 1 (field A z+t • field B z) (field B z) (field B z)
  · exact ae_of_all _ fun z t _ => by
      simpa only [one_mul] using hasDerivAt_gibbsMean 1 (field B z) (field B z) (field A z) t

lemma varianceLine_nonneg (A B : ι → κ → ℝ) (t : ℝ) : 0 ≤ varianceLine A B t :=
  integral_nonneg fun _ => gibbsCov_self_nonneg 1 _ _

lemma monotone_meanLine (A B : ι → κ → ℝ) : Monotone (meanLine A B) := by
  apply monotone_of_hasDerivAt_nonneg (hasDerivAt_meanLine A B)
  intro t
  exact varianceLine_nonneg A B t

lemma convex_expectedLine (A B : ι → κ → ℝ) : ConvexOn ℝ Set.univ (expectedLine A B) := by
  have he : deriv (expectedLine A B)=meanLine A B := funext fun t => (hasDerivAt_expectedLine A B t).deriv
  apply Monotone.convexOn_univ_of_deriv (fun t => (hasDerivAt_expectedLine A B t).differentiableAt)
  rw [he]
  exact monotone_meanLine A B

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

 
def averagedReplica {r : ℕ} (A : ι → κ → ℝ) (f : (Fin r → ι) → ℝ) : ℝ :=
  ∫ z, replicaMean (field A z) f ∂gaussianLaw κ

lemma replicaMean_const {r : ℕ} (x : ι → ℝ) (c : ℝ) :
    replicaMean x (fun _ : Fin r → ι => c)=c := by
  simp [replicaMean, ← Finset.sum_mul, sum_replicaWeight]

omit [Nonempty ι] in
lemma replicaMean_add {r : ℕ} (x : ι → ℝ) (f g : (Fin r → ι) → ℝ) :
    replicaMean x (fun σ => f σ+g σ)=replicaMean x f+replicaMean x g := by
  simp [replicaMean, mul_add, Finset.sum_add_distrib]

omit [Nonempty ι] in
lemma replicaMean_sub {r : ℕ} (x : ι → ℝ) (f g : (Fin r → ι) → ℝ) :
    replicaMean x (fun σ => f σ-g σ)=replicaMean x f-replicaMean x g := by
  simp [replicaMean, mul_sub, Finset.sum_sub_distrib]

omit [Nonempty ι] in
lemma replicaMean_const_mul {r : ℕ} (x : ι → ℝ) (f : (Fin r → ι) → ℝ) (c : ℝ) :
    replicaMean x (fun σ => c*f σ)=c*replicaMean x f := by
  simp [replicaMean, mul_left_comm _ c, Finset.mul_sum]

lemma averagedReplica_const {r : ℕ} (A : ι → κ → ℝ) (c : ℝ) :
    averagedReplica A (fun _ : Fin r → ι => c)=c := by
  simp [averagedReplica, replicaMean_const]

lemma averagedReplica_add {r : ℕ} (A : ι → κ → ℝ) (f g : (Fin r → ι) → ℝ) :
    averagedReplica A (fun σ => f σ+g σ)=averagedReplica A f+averagedReplica A g := by
  simp only [averagedReplica, replicaMean_add]
  exact integral_add (integrable_field_replicaMean A f) (integrable_field_replicaMean A g)

lemma averagedReplica_sub {r : ℕ} (A : ι → κ → ℝ) (f g : (Fin r → ι) → ℝ) :
    averagedReplica A (fun σ => f σ-g σ)=averagedReplica A f-averagedReplica A g := by
  simp only [averagedReplica, replicaMean_sub]
  exact integral_sub (integrable_field_replicaMean A f) (integrable_field_replicaMean A g)

omit [Nonempty ι] in
lemma averagedReplica_const_mul {r : ℕ} (A : ι → κ → ℝ) (f : (Fin r → ι) → ℝ) (c : ℝ) :
    averagedReplica A (fun σ => c*f σ)=c*averagedReplica A f := by
  simp only [averagedReplica, replicaMean_const_mul, integral_const_mul]

lemma averagedReplica_marginal {r : ℕ} (A : ι → κ → ℝ) (f : (Fin r → ι) → ℝ) :
    averagedReplica A (fun τ : Fin (r+1) → ι => f (fun l => τ l.castSucc))=averagedReplica A f := by
  simp only [averagedReplica, replicaMean_marginal]

lemma averagedReplica_sum {r : ℕ} {L : Type*} [Fintype L] (A : ι → κ → ℝ)
    (f : L → (Fin r → ι) → ℝ) :
    averagedReplica A (fun σ => ∑ l, f l σ)=∑ l, averagedReplica A (f l) := by
  have he (z : κ → ℝ) : replicaMean (field A z) (fun σ => ∑ l, f l σ)=
      ∑ l, replicaMean (field A z) (f l) := by
    simp only [replicaMean, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [averagedReplica, he]
  exact integral_finsetSum _ (fun l _ => integrable_field_replicaMean A (f l))

lemma replicaMean_abs_bound {r : ℕ} (x : ι → ℝ) {f : (Fin r → ι) → ℝ} {M : ℝ}
    (h : ∀ σ, |f σ|≤M) : |replicaMean x f|≤M := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ σ, replicaWeight x σ*M := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (replicaWeight_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (h σ) (replicaWeight_nonneg _ _)
    _=M := replicaMean_const x M

lemma averagedReplica_abs_bound {r : ℕ} (A : ι → κ → ℝ) {f : (Fin r → ι) → ℝ} {M : ℝ}
    (h : ∀ σ, |f σ|≤M) : |averagedReplica A f|≤M := by
  apply abs_integral_le_integral_abs.trans
  have hb := integral_mono (integrable_field_replicaMean A f).abs (integrable_const M)
    (fun z => replicaMean_abs_bound (field A z) h)
  simpa using hb

 
def energyMean (A B : ι → κ → ℝ) : ℝ :=
  ∫ z, ∑ s, weight (field A z) s*field B z s ∂gaussianLaw κ

def energyObservation {r : ℕ} (A B : ι → κ → ℝ) (i : Fin r) (f : (Fin r → ι) → ℝ) : ℝ :=
  ∫ z, ∑ σ, replicaWeight (field A z) σ*(field B z (σ i)*f σ) ∂gaussianLaw κ

lemma energyObservation_one {r : ℕ} (A B : ι → κ → ℝ) (i : Fin r) :
    energyObservation A B i (fun _ => 1)=energyMean A B := by
  unfold energyObservation energyMean
  simp only [mul_one]
  apply integral_congr_ae
  exact ae_of_all _ fun z => replicaMean_single (field A z) i (field B z)

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

 
def energyDeviation (A B : ι → κ → ℝ) (c : ℝ) : ℝ :=
  ∫ z, ∑ s, weight (field A z) s*|field B z s-c| ∂gaussianLaw κ

lemma integrable_energyDeviation (A B : ι → κ → ℝ) (c : ℝ) :
    Integrable (fun z => ∑ s, weight (field A z) s*|field B z s-c|) (gaussianLaw κ) := by
  apply integrable_finsetSum
  intro s _
  apply (((integrable_field B s).sub (integrable_const c)).abs).bdd_mul
    ((continuous_weight s).comp (continuous_field A)).aestronglyMeasurable (c:=1)
  exact ae_of_all _ fun z => by
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)]
    exact weight_le_one _ _

lemma energyDeviation_nonneg (A B : ι → κ → ℝ) (c : ℝ) : 0 ≤ energyDeviation A B c := by
  apply integral_nonneg
  intro z
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (weight_pos _ _).le (abs_nonneg _))

lemma energyObservation_sub_mean {r : ℕ} (A B : ι → κ → ℝ) (c : ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) :
    energyObservation A B i f-c*averagedReplica A f =
      ∫ z, replicaMean (field A z) (fun σ => (field B z (σ i)-c)*f σ) ∂gaussianLaw κ := by
  have he (z : κ → ℝ) : replicaMean (field A z) (fun σ => (field B z (σ i)-c)*f σ) =
      (∑ σ, replicaWeight (field A z) σ*(field B z (σ i)*f σ))-
      c*replicaMean (field A z) f := by
    simp only [replicaMean, sub_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp only [he]
  rw [integral_sub (integrable_field_replica_energy A B i f)
    ((integrable_field_replicaMean A f).const_mul c), integral_const_mul]
  rfl

 

theorem energyObservation_covariance_bound {r : ℕ} (A B : ι → κ → ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) {M : ℝ} (_hM : 0≤M) (hf : ∀ σ, |f σ|≤M)
    (c : ℝ) :
    |energyObservation A B i f-c*averagedReplica A f| ≤ M*energyDeviation A B c := by
  rw [energyObservation_sub_mean]
  apply abs_integral_le_integral_abs.trans
  have hd (z : κ → ℝ) :
      |replicaMean (field A z) (fun σ => (field B z (σ i)-c)*f σ)| ≤
        M*∑ s, weight (field A z) s*|field B z s-c| := by
    calc
      _ ≤ ∑ σ, |replicaWeight (field A z) σ*((field B z (σ i)-c)*f σ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ M*replicaMean (field A z) (fun σ => |field B z (σ i)-c|) := by
        simp only [replicaMean, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro σ _
        rw [abs_mul, abs_of_nonneg (replicaWeight_nonneg _ _), abs_mul]
        have h := mul_le_mul_of_nonneg_left (hf σ)
          (mul_nonneg (replicaWeight_nonneg (field A z) σ) (abs_nonneg (field B z (σ i)-c)))
        nlinarith only [h]
      _ = _ := by rw [replicaMean_single (field A z) i (fun s => |field B z s-c|)]
  have hint : Integrable (fun z => replicaMean (field A z)
      (fun σ => (field B z (σ i)-c)*f σ)) (gaussianLaw κ) := by
    apply (((integrable_energyDeviation A B c).const_mul M)).mono' ?_ (ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using hd z)
    unfold replicaMean
    apply Continuous.aestronglyMeasurable
    apply continuous_finsetSum
    intro σ _
    exact ((continuous_replicaWeight σ).comp (continuous_field A)).mul
      ((((continuous_apply (σ i)).comp (continuous_field B)).sub continuous_const).mul_const (f σ))
  have hb := integral_mono hint.abs ((integrable_energyDeviation A B c).const_mul M) hd
  simpa only [integral_const_mul, energyDeviation] using hb

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace GaussianConcentration
open SKGaussian ParisiInterpolation SKCavity

 

lemma integral_abs_centered_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ z, |f z-∫ x, f x ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  have hc := hf.sub (memLp_const (∫ x, f x ∂μ))
  have ha : MemLp (fun z => |f z-∫ x, f x ∂μ|) 2 μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hc.norm
  have hv := variance_nonneg (fun z => |f z-∫ x, f x ∂μ|) μ
  rw [variance_eq_sub ha] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  rw [← variance_eq_integral hf.aemeasurable] at hv
  have hs := Real.sq_sqrt (variance_nonneg f μ)
  have hsn := Real.sqrt_nonneg (variance f μ)
  nlinarith

lemma memLp_logPartition_field {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (A : ι → κ → ℝ) : MemLp (fun z => logPartition (field A z)) 2 (gaussianLaw κ) := by
  have hfield : MemLp (field A) 2 (gaussianLaw κ) := by
    apply memLp_pi_iff.mpr
    intro s
    exact memLp_field_two A s
  have hLip : LipschitzWith 1 (fun x : ι → ℝ => logPartition x-logPartition (0 : ι → ℝ)) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa only [sub_sub_sub_cancel_right] using (logPartition_lipschitz (ι:=ι)).norm_sub_le x y
  have h := hLip.comp_memLp (by simp) hfield
  convert h.add (memLp_const (logPartition (0 : ι → ℝ))) using 1
  ext z
  simp

 

lemma logPartition_absolute_fluctuation {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (A : ι → κ → ℝ) (c : κ → ℝ≥0) (hA : ∀ s k, |A s k|≤c k) :
    (∫ z, |logPartition (field A z)-expected A| ∂gaussianLaw κ) ≤
      Real.sqrt (∑ k, (c k:ℝ)^2) := by
  exact (integral_abs_centered_le_sqrt_variance (memLp_logPartition_field A)).trans
    (Real.sqrt_le_sqrt (variance_field_logPartition_le A c hA))

end GaussianConcentration

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma pSpin_energyMean {n : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ) :
    energyMean (perturbedCoeff n p β a) (perturbationNoise n p) =
      a*(1-averagedReplica (perturbedCoeff n p β a)
        (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^p)) := by
  have h := pSpin_replica_identity hn p β a (0 : Fin 1) (fun _ => 1)
  norm_num only [Nat.cast_one, Fin.castSucc_zero] at h
  change energyObservation (perturbedCoeff n p β a) (perturbationNoise n p) (0 : Fin 1) (fun _ => 1) =
    a*averagedReplica (perturbedCoeff n p β a)
      (fun σ : Fin 1 → Configuration n => 1*∑ l, (overlap (σ 0) (σ l))^p)-
    (1:ℝ)*a*averagedReplica (perturbedCoeff n p β a)
      (fun τ : Fin 2 → Configuration n => 1*(overlap (τ 0) (τ 1))^p) at h
  simp only [energyObservation_one, one_mul, Fin.sum_univ_one, overlap_self hn, one_pow,
    averagedReplica_const] at h
  linarith

 

def pSpinGGDefect {n r : ℕ} (p : ℕ) (β a : ℝ) (i : Fin r)
    (f : (Fin r → Configuration n) → ℝ) : ℝ :=
  (r:ℝ)*averagedReplica (perturbedCoeff n p β a)
      (fun τ : Fin (r+1) → Configuration n => f (fun l => τ l.castSucc)*
        (overlap (τ i.castSucc) (τ (Fin.last r)))^p)-
    averagedReplica (perturbedCoeff n p β a) f*
      averagedReplica (perturbedCoeff n p β a)
        (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^p)-
    averagedReplica (perturbedCoeff n p β a)
      (fun σ => f σ*∑ l ∈ Finset.univ.erase i, (overlap (σ i) (σ l))^p)

 

theorem pSpinGGDefect_identity {n r : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ) :
    a*pSpinGGDefect p β a i f =
      energyMean (perturbedCoeff n p β a) (perturbationNoise n p)*
        averagedReplica (perturbedCoeff n p β a) f-
      energyObservation (perturbedCoeff n p β a) (perturbationNoise n p) i f := by
  have h := pSpin_replica_identity hn p β a i f
  change energyObservation (perturbedCoeff n p β a) (perturbationNoise n p) i f =
    a*averagedReplica (perturbedCoeff n p β a) (fun σ => f σ*∑ l, overlap (σ i) (σ l)^p)-
      (r:ℝ)*a*averagedReplica (perturbedCoeff n p β a)
      (fun τ : Fin (r+1) → Configuration n => f (fun l => τ l.castSucc)*
        overlap (τ i.castSucc) (τ (Fin.last r))^p) at h
  have he (σ : Fin r → Configuration n) : f σ*∑ l, overlap (σ i) (σ l)^p =
      f σ+f σ*∑ l ∈ Finset.univ.erase i, overlap (σ i) (σ l)^p := by
    have hs := Finset.sum_erase_add Finset.univ (fun l => overlap (σ i) (σ l)^p) (Finset.mem_univ i)
    rw [overlap_self hn, one_pow] at hs
    rw [← hs]
    ring
  simp_rw [he, averagedReplica_add] at h
  rw [pSpin_energyMean hn, h]
  unfold pSpinGGDefect
  ring

 

theorem pSpinGGDefect_bound {n r : ℕ} (hn : 0<n) (p : ℕ) (β a : ℝ)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ σ, |f σ|≤M) :
    |a*pSpinGGDefect p β a i f| ≤
      M*energyDeviation (perturbedCoeff n p β a) (perturbationNoise n p)
        (energyMean (perturbedCoeff n p β a) (perturbationNoise n p)) := by
  rw [pSpinGGDefect_identity hn, abs_sub_comm]
  exact energyObservation_covariance_bound _ _ i f hM hf _

end SKCavity

end

end OAI
