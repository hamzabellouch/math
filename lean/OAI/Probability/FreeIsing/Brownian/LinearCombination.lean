import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianLinearCombination

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ι → ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure μ] in

theorem isGaussianProcess_sum
    (hB : ∀ i, IsGaussianProcess (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ) :
    IsGaussianProcess (fun t ω => ∑ i, a i * B i t ω) μ := by
  classical
  constructor
  intro I
  let C : ι → Ω → (I → ℝ) := fun i ω t => a i * B i t ω
  have hC (i : ι) : HasGaussianLaw (C i) μ := by
    exact ((hB i).smul (fun _ => a i)).hasGaussianLaw I
  have hCi : iIndepFun C μ := by
    have h := hind.comp (fun i (x : ℝ≥0 → ℝ) (t : I) => a i * x t)
      (fun i => by fun_prop)
    exact h
  have hsum := hCi.hasGaussianLaw_fun_sum hC
  have heq : (fun ω => ∑ i, C i ω) =
      (fun ω => I.restrict (fun t => ∑ i, a i * B i t ω)) := by
    funext ω t
    simp only [Finset.sum_apply, C, Finset.restrict_def]
  rw [heq] at hsum
  exact hsum

omit [Fintype ι] [IsProbabilityMeasure μ] in

theorem covariance_channel_ne
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ)
    {i j : ι} (hij : i ≠ j) (s t : ℝ≥0) :
    cov[B i s, B j t; μ] = 0 := by
  have h := (hind.indepFun hij).comp (measurable_pi_apply s) (measurable_pi_apply t)
  exact h.covariance_eq_zero
    ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    ((hB j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem covariance_sum
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ)
    (s t : ℝ≥0) :
    cov[fun ω => ∑ i, a i * B i s ω, fun ω => ∑ i, a i * B i t ω; μ] =
      (∑ i, (a i) ^ 2) * (min s t : ℝ≥0) := by
  classical
  rw [covariance_fun_sum_fun_sum
    (fun i => ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two.const_mul (a i))
    (fun i => ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.const_mul (a i))]
  have heq (i j : ι) : cov[fun ω => a i * B i s ω, fun ω => a j * B j t ω; μ] =
      if i = j then (a i) ^ 2 * (min s t : ℝ≥0) else 0 := by
    rw [covariance_const_mul_left, covariance_const_mul_right]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, (hB i).covariance_eval]
      ring
    · rw [ite_eq_right hij, covariance_channel_ne hB hind hij, mul_zero, mul_zero]
  simp_rw [heq]
  simp [Finset.sum_mul]

theorem isPreBrownianReal_sum
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ)
    (ha : ∑ i, (a i) ^ 2 = 1) :
    IsPreBrownianReal (fun t ω => ∑ i, a i * B i t ω) μ := by
  apply (isGaussianProcess_sum (fun i => (hB i).isGaussianProcess) hind a).isPreBrownianReal_of_covariance
  · intro t
    rw [integral_finsetSum _ (fun i _ => ((hB i).integrable_eval t).const_mul (a i))]
    simp_rw [integral_const_mul, IsPreBrownianReal.integral_eval (hB _), mul_zero]
    simp
  · intro s t hst
    rw [covariance_sum hB hind a, ha, one_mul, min_eq_left hst]

theorem isBrownianReal_sum
    (hB : ∀ i, IsBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ)
    (ha : ∑ i, (a i) ^ 2 = 1) :
    IsBrownianReal (fun t ω => ∑ i, a i * B i t ω) μ := by
  refine ⟨isPreBrownianReal_sum (fun i => (hB i).toIsPreBrownianReal) hind a ha, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => (hB i).cont)] with ω hω
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hω i))

theorem isPreBrownianReal_normalized_sum
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ)
    (ha : 0 < ∑ i, (a i) ^ 2) :
    IsPreBrownianReal
      (fun t ω => (Real.sqrt (∑ i, (a i) ^ 2))⁻¹ * ∑ i, a i * B i t ω) μ := by
  have hnorm : ∑ i, (a i / Real.sqrt (∑ j, (a j) ^ 2)) ^ 2 = 1 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt ha.le, div_self ha.ne']
  have h := isPreBrownianReal_sum hB hind
    (fun i => a i / Real.sqrt (∑ j, (a j) ^ 2)) hnorm
  convert h using 1
  funext t ω
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv]
  ring

omit [IsProbabilityMeasure μ] in

theorem ae_abs_sum_le {A : ι → Ω → ℝ} (a : ι → ℝ) {R : ℝ}
    (hA : ∀ i, ∀ᵐ ω ∂μ, |A i ω| ≤ R) :
    ∀ᵐ ω ∂μ, |∑ i, a i * A i ω| ≤ (∑ i, |a i|) * R := by
  filter_upwards [ae_all_iff.mpr hA] with ω hω
  calc
    |∑ i, a i * A i ω| ≤ ∑ i, |a i * A i ω| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |A i ω| := by simp only [abs_mul]
    _ ≤ ∑ i, |a i| * R :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hω i) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

omit [IsProbabilityMeasure μ] in
theorem martingale_sum {T : Type*} [Preorder T]
    (F : Filtration T ‹MeasurableSpace Ω›) {M : ι → T → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (a : ι → ℝ) :
    Martingale (fun t ω => ∑ i, a i * M i t ω) F μ := by
  classical
  have hsum (s : Finset ι) : Martingale (fun t ω => ∑ i ∈ s, a i * M i t ω) F μ := by
    induction s using Finset.induction_on with
    | empty =>
      have heq : (fun t ω => ∑ i ∈ (∅ : Finset ι), a i * M i t ω) =
          (0 : T → Ω → ℝ) := by funext t ω; simp
      rw [heq]
      exact martingale_zero ℝ F μ
    | @insert i s hi ih =>
      have h := ((hM i).smul (a i)).add ih
      have heq : a i • M i + (fun t ω => ∑ j ∈ s, a j * M j t ω) =
          (fun t ω => ∑ j ∈ insert i s, a j * M j t ω) := by
        funext t ω
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_insert hi]
      rw [heq] at h
      exact h
  exact hsum Finset.univ

end Problem367.BrownianLinearCombination

end

end OAI
