import Mathlib

namespace OAI

/-! Spin. -/

noncomputable section


 

 

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace SKFluctuations

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

def hamiltonian (beta : ℝ) (n : ℕ) (g : Disorder n) (sigma : Spin n) : ℝ :=
  beta / Real.sqrt (n : ℝ) *
    ∑ e : Edge n, g e * spinValue (sigma e.val.1) * spinValue (sigma e.val.2)

def partitionFunction (beta : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ sigma : Spin n, Real.exp (hamiltonian beta n g sigma)

def freeEnergy (beta : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  Real.log (partitionFunction beta n g)

def meanFreeEnergy (beta : ℝ) (n : ℕ) : ℝ :=
  ∫ g, freeEnergy beta n g ∂disorderLaw n

def freeEnergyVariance (beta : ℝ) (n : ℕ) : ℝ :=
  variance (freeEnergy beta n) (disorderLaw n)

def freeEnergySD (beta : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (freeEnergyVariance beta n)

def fluctuationEvent (beta eta : ℝ) (n : ℕ) : Set (Disorder n) :=
  {g | (n : ℝ) ^ ((1 : ℝ) / 6 - eta) ≤ |freeEnergy beta n g - meanFreeEnergy beta n| ∧
    |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ) ^ ((1 : ℝ) / 6 + eta)}

instance disorderLaw_isProbability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  infer_instance

@[simp] theorem abs_spinValue (b : Bool) : |spinValue b| = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] theorem card_spin (n : ℕ) : Fintype.card (Spin n) = 2 ^ n := by
  simp [Spin]

 
theorem prior_mass (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℤ)) * (Fintype.card (Spin n) : ℝ) = 1 := by
  rw [card_spin]
  simp [zpow_neg, zpow_natCast]

theorem continuous_hamiltonian (beta : ℝ) (n : ℕ) (sigma : Spin n) :
    Continuous (fun g => hamiltonian beta n g sigma) := by
  unfold hamiltonian
  fun_prop

theorem continuous_partitionFunction (beta : ℝ) (n : ℕ) :
    Continuous (partitionFunction beta n) := by
  unfold partitionFunction
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro sigma _
  exact Real.continuous_exp.comp (continuous_hamiltonian beta n sigma)

theorem partitionFunction_pos (beta : ℝ) (n : ℕ) (g : Disorder n) :
    0 < partitionFunction beta n g := by
  apply mul_pos (zpow_pos (by norm_num) _)
  exact Finset.sum_pos (fun sigma _ => Real.exp_pos _) Finset.univ_nonempty

theorem continuous_freeEnergy (beta : ℝ) (n : ℕ) :
    Continuous (freeEnergy beta n) :=
  (continuous_partitionFunction beta n).log (fun g => ne_of_gt (partitionFunction_pos beta n g))

 
def disorderSize (beta : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  |beta / Real.sqrt (n : ℝ)| * ∑ e : Edge n, |g e|

theorem abs_hamiltonian_le (beta : ℝ) (n : ℕ) (g : Disorder n) (sigma : Spin n) :
    |hamiltonian beta n g sigma| ≤ disorderSize beta n g := by
  unfold hamiltonian disorderSize
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    |∑ e : Edge n, g e * spinValue (sigma e.val.1) * spinValue (sigma e.val.2)|
        ≤ ∑ e : Edge n, |g e * spinValue (sigma e.val.1) * spinValue (sigma e.val.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e : Edge n, |g e| := by simp [abs_mul]

theorem partitionFunction_le (beta : ℝ) (n : ℕ) (g : Disorder n) :
    partitionFunction beta n g ≤ Real.exp (disorderSize beta n g) := by
  calc
    partitionFunction beta n g ≤ (2 : ℝ) ^ (-(n : ℤ)) *
        ∑ _sigma : Spin n, Real.exp (disorderSize beta n g) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (zpow_pos (by norm_num) _))
      apply Finset.sum_le_sum
      intro sigma _
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_hamiltonian_le beta n g sigma))
    _ = Real.exp (disorderSize beta n g) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, prior_mass, one_mul]

theorem le_partitionFunction (beta : ℝ) (n : ℕ) (g : Disorder n) :
    Real.exp (-disorderSize beta n g) ≤ partitionFunction beta n g := by
  calc
    Real.exp (-disorderSize beta n g) = (2 : ℝ) ^ (-(n : ℤ)) *
        ∑ _sigma : Spin n, Real.exp (-disorderSize beta n g) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, prior_mass, one_mul]
    _ ≤ partitionFunction beta n g := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (zpow_pos (by norm_num) _))
      apply Finset.sum_le_sum
      intro sigma _
      apply Real.exp_le_exp.mpr
      exact (neg_le_neg (abs_hamiltonian_le beta n g sigma)).trans (neg_abs_le _)

theorem abs_freeEnergy_le (beta : ℝ) (n : ℕ) (g : Disorder n) :
    |freeEnergy beta n g| ≤ disorderSize beta n g := by
  apply abs_le.mpr
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) (le_partitionFunction beta n g)
    simpa [freeEnergy] using h
  · have h := Real.log_le_log (partitionFunction_pos beta n g) (partitionFunction_le beta n g)
    simpa [freeEnergy] using h

theorem memLp_disorderSize (beta : ℝ) (n : ℕ) :
    MemLp (disorderSize beta n) 2 (disorderLaw n) := by
  have he (e : Edge n) : MemLp (fun g : Disorder n => g e) 2 (disorderLaw n) := by
    simpa [disorderLaw, Function.comp_def] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) (2 : NNReal)).comp_measurePreserving
        (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 1) e)
  exact (memLp_finsetSum Finset.univ (fun e _ => (he e).abs)).const_mul _

theorem memLp_freeEnergy (beta : ℝ) (n : ℕ) :
    MemLp (freeEnergy beta n) 2 (disorderLaw n) := by
  apply (memLp_disorderSize beta n).mono'
    (continuous_freeEnergy beta n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun g => by
    simpa only [Real.norm_eq_abs] using abs_freeEnergy_le beta n g)

theorem integrable_freeEnergy (beta : ℝ) (n : ℕ) :
    Integrable (freeEnergy beta n) (disorderLaw n) :=
  (memLp_freeEnergy beta n).integrable (by norm_num)

theorem freeEnergyVariance_eq_integral (beta : ℝ) (n : ℕ) :
    freeEnergyVariance beta n =
      ∫ g, (freeEnergy beta n g - meanFreeEnergy beta n) ^ 2 ∂disorderLaw n := by
  exact variance_eq_integral (continuous_freeEnergy beta n).aemeasurable

theorem freeEnergyVariance_nonneg (beta : ℝ) (n : ℕ) :
    0 ≤ freeEnergyVariance beta n := variance_nonneg _ _

 
theorem integrable_exp_mul_abs_gaussian (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * |x|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-t))).mono'
  · exact (Real.continuous_exp.comp (continuous_abs.const_mul t)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change Real.exp (t * |x|) ≤ Real.exp (t * x) + Real.exp (-t * x)
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hx, mul_neg, neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)

 
theorem integrable_exp_disorderSize (beta t : ℝ) (n : ℕ) :
    Integrable (fun g => Real.exp (t * disorderSize beta n g)) (disorderLaw n) := by
  have h := Integrable.fintype_prod (fun _e : Edge n =>
    integrable_exp_mul_abs_gaussian (t * |beta / Real.sqrt (n : ℝ)|))
  have heq (g : Disorder n) : Real.exp (t * disorderSize beta n g) =
      ∏ e : Edge n, Real.exp ((t * |beta / Real.sqrt (n : ℝ)|) * |g e|) := by
    simp only [disorderSize, ← mul_assoc, Finset.mul_sum, Real.exp_sum]
  simp_rw [heq]
  exact h

 
theorem integrable_exp_freeEnergy (beta t : ℝ) (n : ℕ) :
    Integrable (fun g => Real.exp (t * freeEnergy beta n g)) (disorderLaw n) := by
  apply (integrable_exp_disorderSize beta |t| n).mono'
  · exact (Real.continuous_exp.comp
      ((continuous_freeEnergy beta n).const_mul t)).aestronglyMeasurable
  · filter_upwards [] with g
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * freeEnergy beta n g ≤ |t * freeEnergy beta n g| := le_abs_self _
      _ = |t| * |freeEnergy beta n g| := abs_mul _ _
      _ ≤ |t| * disorderSize beta n g :=
        mul_le_mul_of_nonneg_left (abs_freeEnergy_le beta n g) (abs_nonneg _)

 

def finiteLogSumExp {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) : ℝ :=
  Real.log (c * ∑ i, Real.exp (x i))

theorem finite_partition_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) (x : ι → ℝ) : 0 < c * ∑ i, Real.exp (x i) :=
  mul_pos hc (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)

theorem normalized_exp_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) (x : ι → ℝ) :
    c * ∑ i, Real.exp (x i - finiteLogSumExp c x) = 1 := by
  simp_rw [Real.exp_sub, finiteLogSumExp,
    Real.exp_log (finite_partition_pos hc x), ← Finset.sum_div]
  rw [← mul_div_assoc, div_self (ne_of_gt (finite_partition_pos hc x))]

 

theorem convex_finiteLogSumExp {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) : ConvexOn ℝ Set.univ (finiteLogSumExp (ι := ι) c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let A := finiteLogSumExp c x
  let B := finiteLogSumExp c y
  have hsum : c * ∑ i, Real.exp (a * (x i - A) + b * (y i - B)) ≤ 1 := by
    calc
      _ ≤ c * ∑ i, (a * Real.exp (x i - A) + b * Real.exp (y i - B)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        apply Finset.sum_le_sum
        intro i _
        exact convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ = a * (c * ∑ i, Real.exp (x i - A)) +
          b * (c * ∑ i, Real.exp (y i - B)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      _ = 1 := by rw [normalized_exp_sum hc x, normalized_exp_sum hc y]; linarith
  have heq : c * ∑ i, Real.exp (a * (x i - A) + b * (y i - B)) =
      Real.exp (finiteLogSumExp c (a • x + b • y) - (a * A + b * B)) := by
    have harg (i : ι) : a * (x i - A) + b * (y i - B) =
        (a • x + b • y) i - (a * A + b * B) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [harg, Real.exp_sub, ← Finset.sum_div]
    rw [finiteLogSumExp, Real.exp_log (finite_partition_pos hc _), ← mul_div_assoc]
  rw [heq] at hsum
  have := Real.exp_le_one_iff.mp hsum
  change finiteLogSumExp c (a • x + b • y) ≤ a * A + b * B
  linarith

theorem hamiltonian_add (beta : ℝ) (n : ℕ) (g h : Disorder n) (sigma : Spin n) :
    hamiltonian beta n (g + h) sigma =
      hamiltonian beta n g sigma + hamiltonian beta n h sigma := by
  simp only [hamiltonian, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem hamiltonian_smul (beta c : ℝ) (n : ℕ) (g : Disorder n) (sigma : Spin n) :
    hamiltonian beta n (c • g) sigma = c * hamiltonian beta n g sigma := by
  simp only [hamiltonian, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

 

theorem convex_freeEnergy (beta : ℝ) (n : ℕ) :
    ConvexOn ℝ Set.univ (freeEnergy beta n) := by
  refine ⟨convex_univ, ?_⟩
  intro g _ h _ a b ha hb hab
  have hcv := (convex_finiteLogSumExp (ι := Spin n)
    (zpow_pos (show (0 : ℝ) < 2 by norm_num) (-(n : ℤ)))).2
    (x := hamiltonian beta n g) (y := hamiltonian beta n h)
    (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hlin : hamiltonian beta n (a • g + b • h) =
      a • hamiltonian beta n g + b • hamiltonian beta n h := by
    ext sigma
    simp only [hamiltonian_add, hamiltonian_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [freeEnergy, partitionFunction, finiteLogSumExp, hlin] using hcv

 
def completionVariance (beta : ℝ) : NNReal := ⟨beta ^ 2 / 2, by positivity⟩

def completedLaw (beta : ℝ) (n : ℕ) : Measure (Disorder n × ℝ) :=
  (disorderLaw n).prod (gaussianReal 0 (completionVariance beta))

def completedFreeEnergy (beta : ℝ) (n : ℕ) (g : Disorder n × ℝ) : ℝ :=
  freeEnergy beta n g.1 + g.2

instance completedLaw_isProbability (beta : ℝ) (n : ℕ) :
    IsProbabilityMeasure (completedLaw beta n) := by
  unfold completedLaw
  infer_instance

theorem memLp_completedFreeEnergy (beta : ℝ) (n : ℕ) :
    MemLp (completedFreeEnergy beta n) 2 (completedLaw beta n) := by
  exact ((memLp_freeEnergy beta n).comp_fst _).add
    ((memLp_id_gaussianReal (2 : NNReal)).comp_snd _)

theorem integrable_completedFreeEnergy (beta : ℝ) (n : ℕ) :
    Integrable (completedFreeEnergy beta n) (completedLaw beta n) :=
  (memLp_completedFreeEnergy beta n).integrable (by norm_num)

theorem mean_completedFreeEnergy (beta : ℝ) (n : ℕ) :
    ∫ g, completedFreeEnergy beta n g ∂completedLaw beta n = meanFreeEnergy beta n := by
  have hD : Integrable (fun x : ℝ => x) (gaussianReal 0 (completionVariance beta)) :=
    (memLp_id_gaussianReal (μ := 0) (v := completionVariance beta)
      (2 : NNReal)).integrable (by norm_num : (1 : ENNReal) ≤ (2 : NNReal))
  unfold completedFreeEnergy completedLaw
  rw [integral_add ((integrable_freeEnergy beta n).comp_fst _) (hD.comp_snd _)]
  rw [integral_fun_fst, integral_fun_snd (f := fun x : ℝ => x)]
  simp [Measure.real, meanFreeEnergy]

theorem variance_completedFreeEnergy (beta : ℝ) (n : ℕ) :
    variance (completedFreeEnergy beta n) (completedLaw beta n) =
      freeEnergyVariance beta n + beta ^ 2 / 2 := by
  have h := variance_add_prod (memLp_freeEnergy beta n)
    (memLp_id_gaussianReal (μ := 0) (v := completionVariance beta) (2 : NNReal))
  rw [variance_id_gaussianReal] at h
  exact h

 
theorem mgf_completedFreeEnergy (beta t : ℝ) (n : ℕ) :
    mgf (completedFreeEnergy beta n) (completedLaw beta n) t =
      mgf (freeEnergy beta n) (disorderLaw n) t * Real.exp (beta ^ 2 * t ^ 2 / 4) := by
  simp only [mgf, completedFreeEnergy, completedLaw, mul_add, Real.exp_add]
  rw [integral_prod_mul (fun g => Real.exp (t * freeEnergy beta n g))
    (fun x : ℝ => Real.exp (t * x))]
  have hg := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := completionVariance beta)) t
  simp only [mgf, zero_mul, zero_add] at hg
  rw [hg]
  congr 2
  change (beta ^ 2 / 2) * t ^ 2 / 2 = beta ^ 2 * t ^ 2 / 4
  ring

theorem integrable_exp_completedFreeEnergy (beta t : ℝ) (n : ℕ) :
    Integrable (fun g => Real.exp (t * completedFreeEnergy beta n g))
      (completedLaw beta n) := by
  simpa only [completedFreeEnergy, completedLaw, mul_add, Real.exp_add] using
    (integrable_exp_freeEnergy beta t n).mul_prod
      (integrable_exp_mul_gaussianReal (μ := 0) (v := completionVariance beta) t)

 
def laplaceTransform (beta t : ℝ) (n : ℕ) : ℝ :=
  ∫ g, Real.exp (t * (freeEnergy beta n g - meanFreeEnergy beta n)) ∂disorderLaw n

def completedLaplaceTransform (beta t : ℝ) (n : ℕ) : ℝ :=
  ∫ g, Real.exp (t * (completedFreeEnergy beta n g - meanFreeEnergy beta n))
    ∂completedLaw beta n

theorem laplaceTransform_eq (beta t : ℝ) (n : ℕ) :
    laplaceTransform beta t n =
      Real.exp (-t * meanFreeEnergy beta n) * mgf (freeEnergy beta n) (disorderLaw n) t := by
  simp_rw [laplaceTransform, mul_sub, Real.exp_sub]
  rw [integral_div]
  simp only [mgf, Real.exp_neg, neg_mul, div_eq_mul_inv, mul_comm]

theorem completedLaplaceTransform_eq (beta t : ℝ) (n : ℕ) :
    completedLaplaceTransform beta t n =
      laplaceTransform beta t n * Real.exp (beta ^ 2 * t ^ 2 / 4) := by
  simp_rw [completedLaplaceTransform, mul_sub, Real.exp_sub]
  rw [integral_div]
  change mgf (completedFreeEnergy beta n) (completedLaw beta n) t /
    Real.exp (t * meanFreeEnergy beta n) = _
  rw [mgf_completedFreeEnergy, laplaceTransform_eq]
  simp only [neg_mul, Real.exp_neg, div_eq_mul_inv]
  ring

 
def centeredLogLaplace (beta t : ℝ) (n : ℕ) : ℝ :=
  Real.log (laplaceTransform beta t n)

def completedCenteredLogLaplace (beta t : ℝ) (n : ℕ) : ℝ :=
  Real.log (completedLaplaceTransform beta t n)

theorem laplaceTransform_pos (beta t : ℝ) (n : ℕ) :
    0 < laplaceTransform beta t n := by
  rw [laplaceTransform_eq]
  exact mul_pos (Real.exp_pos _) (mgf_pos (integrable_exp_freeEnergy beta t n))

 
theorem completedCenteredLogLaplace_eq (beta t : ℝ) (n : ℕ) :
    completedCenteredLogLaplace beta t n =
      centeredLogLaplace beta t n + beta ^ 2 * t ^ 2 / 4 := by
  unfold completedCenteredLogLaplace centeredLogLaplace
  rw [completedLaplaceTransform_eq, Real.log_mul (laplaceTransform_pos beta t n).ne'
    (Real.exp_pos _).ne', Real.log_exp]

def centeredFreeEnergy (beta : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  freeEnergy beta n g - meanFreeEnergy beta n

theorem integral_centeredFreeEnergy (beta : ℝ) (n : ℕ) :
    ∫ g, centeredFreeEnergy beta n g ∂disorderLaw n = 0 := by
  unfold centeredFreeEnergy
  rw [integral_sub (integrable_freeEnergy beta n) (integrable_const _)]
  simp [meanFreeEnergy, Measure.real]

theorem integrable_centeredFreeEnergy (beta : ℝ) (n : ℕ) :
    Integrable (centeredFreeEnergy beta n) (disorderLaw n) :=
  (integrable_freeEnergy beta n).sub (integrable_const _)

theorem integrable_exp_centeredFreeEnergy (beta t : ℝ) (n : ℕ) :
    Integrable (fun g => Real.exp (t * centeredFreeEnergy beta n g)) (disorderLaw n) := by
  simp_rw [centeredFreeEnergy, mul_sub, Real.exp_sub]
  exact (integrable_exp_freeEnergy beta t n).div_const _

theorem one_le_laplaceTransform (beta t : ℝ) (n : ℕ) :
    1 ≤ laplaceTransform beta t n := by
  have h := integral_mono
    (((integrable_centeredFreeEnergy beta n).const_mul t).add (integrable_const 1))
    (integrable_exp_centeredFreeEnergy beta t n)
    (fun g => Real.add_one_le_exp (t * centeredFreeEnergy beta n g))
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_centeredFreeEnergy beta n).const_mul t)
    (integrable_const 1), integral_const_mul, integral_centeredFreeEnergy] at h
  simpa [Measure.real, laplaceTransform, centeredFreeEnergy] using h

theorem centeredLogLaplace_nonneg (beta t : ℝ) (n : ℕ) :
    0 ≤ centeredLogLaplace beta t n :=
  Real.log_nonneg (one_le_laplaceTransform beta t n)

theorem integrableExpSet_centeredFreeEnergy (beta : ℝ) (n : ℕ) :
    integrableExpSet (centeredFreeEnergy beta n) (disorderLaw n) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_exp_centeredFreeEnergy beta t n

theorem centeredLogLaplace_eq_cgf (beta : ℝ) (n : ℕ) :
    (fun t => centeredLogLaplace beta t n) =
      cgf (centeredFreeEnergy beta n) (disorderLaw n) := rfl

 
theorem analyticAt_centeredLogLaplace (beta t : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun s => centeredLogLaplace beta s n) t := by
  rw [centeredLogLaplace_eq_cgf]
  apply analyticAt_cgf
  simp [integrableExpSet_centeredFreeEnergy]

 

theorem exists_centeredLogLaplace_eq_secondDeriv (beta t : ℝ) (n : ℕ) (ht : 0 < t) :
    ∃ u ∈ Set.Ioo 0 t, centeredLogLaplace beta t n =
      iteratedDeriv 2 (fun s => centeredLogLaplace beta s n) u * t ^ 2 / 2 := by
  change ∃ u ∈ Set.Ioo 0 t, cgf (centeredFreeEnergy beta n) (disorderLaw n) t =
    iteratedDeriv 2 (cgf (centeredFreeEnergy beta n) (disorderLaw n)) u * t ^ 2 / 2
  apply exists_cgf_eq_iteratedDeriv_two_cgf_mul ht (integral_centeredFreeEnergy beta n)
  simp [integrableExpSet_centeredFreeEnergy]

 

def PositiveLaplaceWindow : Prop :=
  ∀ beta : ℝ, 1 < beta → ∀ m : ℝ, 0 < m → m < 1 / 300 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      c * (n : ℝ) ^ (20 * m) ≤
        completedCenteredLogLaplace beta ((n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m)) n ∧
      completedCenteredLogLaplace beta ((n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m)) n ≤
        C * (n : ℝ) ^ (100 * m)

 
def spinGauge {n : ℕ} (tau : Spin n) : Spin n ≃ Spin n where
  toFun sigma i := (tau i == sigma i)
  invFun sigma i := (tau i == sigma i)
  left_inv sigma := by
    funext i
    change (tau i == (tau i == sigma i)) = sigma i
    cases tau i <;> cases sigma i <;> rfl
  right_inv sigma := by
    funext i
    change (tau i == (tau i == sigma i)) = sigma i
    cases tau i <;> cases sigma i <;> rfl

@[simp] theorem spinValue_beq (a b : Bool) :
    spinValue (a == b) = spinValue a * spinValue b := by
  cases a <;> cases b <;> norm_num [spinValue]

@[simp] theorem spinValue_sq (b : Bool) : spinValue b * spinValue b = 1 := by
  cases b <;> norm_num [spinValue]

 
def gaugeDisorder {n : ℕ} (tau : Spin n) (g : Disorder n) : Disorder n :=
  fun e => g e * spinValue (tau e.val.1) * spinValue (tau e.val.2)

theorem hamiltonian_gauge (beta : ℝ) (n : ℕ) (tau sigma : Spin n) (g : Disorder n) :
    hamiltonian beta n (gaugeDisorder tau g) sigma =
      hamiltonian beta n g (spinGauge tau sigma) := by
  unfold hamiltonian
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  simp only [gaugeDisorder, spinGauge, Equiv.coe_fn_mk, spinValue_beq]
  ring

@[simp] theorem partitionFunction_gauge (beta : ℝ) (n : ℕ) (tau : Spin n)
    (g : Disorder n) : partitionFunction beta n (gaugeDisorder tau g) =
      partitionFunction beta n g := by
  simp only [partitionFunction, hamiltonian_gauge]
  congr 1
  exact Equiv.sum_comp (spinGauge tau) (fun sigma => Real.exp (hamiltonian beta n g sigma))

@[simp] theorem freeEnergy_gauge (beta : ℝ) (n : ℕ) (tau : Spin n)
    (g : Disorder n) : freeEnergy beta n (gaugeDisorder tau g) = freeEnergy beta n g := by
  simp only [freeEnergy, partitionFunction_gauge]

theorem spinGauge_transitive {n : ℕ} (sigma rho : Spin n) :
    ∃ tau : Spin n, spinGauge tau sigma = rho := by
  refine ⟨fun i => (sigma i == rho i), ?_⟩
  funext i
  change ((sigma i == rho i) == sigma i) = rho i
  cases sigma i <;> cases rho i <;> rfl

theorem gaussianReal_map_spinSigns (a b : Bool) :
    (gaussianReal 0 1).map (fun x : ℝ => x * spinValue a * spinValue b) =
      gaussianReal 0 1 := by
  cases a <;> cases b <;>
    simp [spinValue, gaussianReal_map_neg]

 
theorem measurePreserving_gaugeDisorder {n : ℕ} (tau : Spin n) :
    MeasurePreserving (gaugeDisorder tau) (disorderLaw n) (disorderLaw n) := by
  refine ⟨by unfold gaugeDisorder; fun_prop, ?_⟩
  unfold disorderLaw gaugeDisorder
  rw [Measure.pi_map_pi (f := fun e : Edge n =>
    fun x : ℝ => x * spinValue (tau e.val.1) * spinValue (tau e.val.2))
      (fun _ => by fun_prop)]
  simp only [gaussianReal_map_spinSigns]

 

def MainFluctuationStatement : Prop :=
  ∀ beta : ℝ, 1 < beta →
    (∀ eta : ℝ, 0 < eta → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 : ℝ) / 6 - eta) ≤ freeEnergySD beta n ∧
      freeEnergySD beta n ≤ (n : ℝ) ^ ((1 : ℝ) / 6 + eta)) ∧
    (∀ eta : ℝ, 0 < eta → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 : ℝ) / 3 - eta) ≤ freeEnergyVariance beta n ∧
      freeEnergyVariance beta n ≤ (n : ℝ) ^ ((1 : ℝ) / 3 + eta)) ∧
    (∀ eta : ℝ, 0 < eta →
      Tendsto (fun n : ℕ => disorderLaw n (fluctuationEvent beta eta n)) atTop (𝓝 1))

end SKFluctuations

end

end OAI
