import OAI.Probability.FreeIsing.Estimates.LinearEstimator

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem367

variable {Ω ι : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem memLp_weighted_sum (s : Finset ι) (w : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    MemLp (fun ω => ∑ i ∈ s, w i * X i ω) 2 μ :=
  memLp_finsetSum s (fun i hi => (hX i hi).const_mul (w i))

theorem integral_mul_weighted_sum (s : Finset ι) (w : ι → ℝ)
    {R : Ω → ℝ} (X : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    (∫ ω, R ω * (∑ i ∈ s, w i * X i ω) ∂μ) =
      ∑ i ∈ s, w i * ∫ ω, R ω * X i ω ∂μ := by
  simp_rw [Finset.mul_sum]
  have hi : ∀ i ∈ s, Integrable (fun ω => R ω * (w i * X i ω)) μ :=
    fun i hi => hR.integrable_mul ((hX i hi).const_mul (w i))
  rw [integral_finsetSum s hi]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∫ ω, R ω * (w i * X i ω) ∂μ) = ∫ ω, w i * (R ω * X i ω) ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := integral_const_mul _ _

theorem integral_weighted_sum_sq (s : Finset ι) (w : ι → ℝ)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    (∫ ω, (∑ i ∈ s, w i * X i ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * ∫ ω, X i ω * X j ω ∂μ := by
  let Z : Ω → ℝ := fun ω => ∑ i ∈ s, w i * X i ω
  have hZ := memLp_weighted_sum s w X hX
  calc
    (∫ ω, Z ω ^ 2 ∂μ) = ∑ i ∈ s, w i * ∫ ω, Z ω * X i ω ∂μ := by
      simpa only [pow_two] using integral_mul_weighted_sum s w X hZ hX
    _ = ∑ i ∈ s, w i * ∫ ω, X i ω * Z ω ∂μ := by
      simp_rw [mul_comm (Z _) (X _ _)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_weighted_sum s w X (hX i hi) hX, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem integral_mul_centered_noise {S B : Ω → ℝ}
    (hS : MemLp S 2 μ) (hB : MemLp B 2 μ)
    (hSB : IndepFun S B μ) (hmean : ∫ ω, B ω ∂μ = 0) :
    (∫ ω, S ω * B ω ∂μ) = 0 := by
  rw [hSB.integral_fun_mul_eq_mul_integral hS.aestronglyMeasurable
    hB.aestronglyMeasurable, hmean, mul_zero]

theorem integral_observation_mul_observation
    {S T B C : Ω → ℝ} (hS : MemLp S 2 μ) (hT : MemLp T 2 μ)
    (hB : MemLp B 2 μ) (hC : MemLp C 2 μ)
    (hSC : IndepFun S C μ) (hTB : IndepFun T B μ)
    (hBzero : ∫ ω, B ω ∂μ = 0) (hCzero : ∫ ω, C ω ∂μ = 0) (t : ℝ) :
    (∫ ω, (t * S ω + B ω) * (t * T ω + C ω) ∂μ) =
      t ^ 2 * (∫ ω, S ω * T ω ∂μ) + ∫ ω, B ω * C ω ∂μ := by
  have h1 : Integrable (fun ω => t ^ 2 * (S ω * T ω)) μ :=
    (hS.integrable_mul hT).const_mul (t ^ 2)
  have h2 : Integrable (fun ω => t * (S ω * C ω)) μ :=
    (hS.integrable_mul hC).const_mul t
  have h3 : Integrable (fun ω => t * (T ω * B ω)) μ :=
    (hT.integrable_mul hB).const_mul t
  have h4 : Integrable (fun ω => B ω * C ω) μ := hB.integrable_mul hC
  calc
    _ = ∫ ω, ((t ^ 2 * (S ω * T ω) + t * (S ω * C ω)) +
          t * (T ω * B ω)) + B ω * C ω ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := by
      have h12 : Integrable (fun ω => t ^ 2 * (S ω * T ω) + t * (S ω * C ω)) μ :=
        h1.add h2
      have h123 : Integrable (fun ω => t ^ 2 * (S ω * T ω) + t * (S ω * C ω) +
          t * (T ω * B ω)) μ := h12.add h3
      rw [integral_add h123 h4,
        integral_add h12 h3, integral_add h1 h2]
      simp_rw [integral_const_mul]
      rw [integral_mul_centered_noise hS hC hSC hCzero,
        integral_mul_centered_noise hT hB hTB hBzero]
      ring

theorem integral_signal_mul_observation {R S B : Ω → ℝ}
    (hR : MemLp R 2 μ) (hS : MemLp S 2 μ) (hB : MemLp B 2 μ)
    (hRB : IndepFun R B μ) (hBzero : ∫ ω, B ω ∂μ = 0) (t : ℝ) :
    (∫ ω, R ω * (t * S ω + B ω) ∂μ) =
      t * ∫ ω, R ω * S ω ∂μ := by
  simp_rw [mul_add]
  have h1 : Integrable (fun ω => R ω * (t * S ω)) μ := hR.integrable_mul (hS.const_mul t)
  have h2 : Integrable (fun ω => R ω * B ω) μ := hR.integrable_mul hB
  rw [integral_add h1 h2,
    integral_mul_centered_noise hR hB hRB hBzero, add_zero]
  calc
    (∫ ω, R ω * (t * S ω) ∂μ) = ∫ ω, t * (R ω * S ω) ∂μ := by
      congr 1
      funext ω
      ring
    _ = _ := integral_const_mul _ _

theorem integral_noise_mul_noise [DecidableEq ι] (B : ι → Ω → ℝ)
    (hB : ∀ i, MemLp (B i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hzero : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (t : ℝ) (hsecond : ∀ i, ∫ ω, B i ω ^ 2 ∂μ = t) (i j : ι) :
    (∫ ω, B i ω * B j ω ∂μ) = if i = j then t else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [↓reduceIte, pow_two] using hsecond i
  · rw [ite_eq_right hij]
    exact integral_mul_centered_noise (hB i) (hB j) (hind hij) (hzero j)

theorem integral_weighted_noise_sq [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (B : ι → Ω → ℝ) (hB : ∀ i, MemLp (B i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hzero : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (t : ℝ) (hsecond : ∀ i, ∫ ω, B i ω ^ 2 ∂μ = t) :
    (∫ ω, (∑ i ∈ s, w i * B i ω) ^ 2 ∂μ) = t * ∑ i ∈ s, w i ^ 2 := by
  rw [integral_weighted_sum_sq s w B (fun i _ => hB i)]
  simp_rw [integral_noise_mul_noise B hB hind hzero t hsecond]
  calc
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (if i = j then t else 0)) =
        ∑ i ∈ s, w i * w i * t := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [mul_ite, hi]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem integral_signal_mul_weighted_observation (s : Finset ι) (w : ι → ℝ)
    {R : Ω → ℝ} (S B : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hS : ∀ i ∈ s, MemLp (S i) 2 μ) (hB : ∀ i ∈ s, MemLp (B i) 2 μ)
    (hind : ∀ i ∈ s, IndepFun R (B i) μ)
    (hzero : ∀ i ∈ s, ∫ ω, B i ω ∂μ = 0) (t : ℝ) :
    (∫ ω, R ω * (∑ i ∈ s, w i * (t * S i ω + B i ω)) ∂μ) =
      t * ∑ i ∈ s, w i * ∫ ω, R ω * S i ω ∂μ := by
  rw [integral_mul_weighted_sum s w (fun i ω => t * S i ω + B i ω) hR
    (fun i hi => ((hS i hi).const_mul t).add (hB i hi)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_signal_mul_observation hR (hS i hi) (hB i hi) (hind i hi) (hzero i hi) t]
  ring

theorem integral_weighted_observation_sq [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (S B : ι → Ω → ℝ)
    (hS : ∀ i, MemLp (S i) 2 μ) (hB : ∀ i, MemLp (B i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hSB : ∀ i j, IndepFun (S i) (B j) μ)
    (hzero : ∀ i, ∫ ω, B i ω ∂μ = 0)
    (t : ℝ) (hsecond : ∀ i, ∫ ω, B i ω ^ 2 ∂μ = t) :
    (∫ ω, (∑ i ∈ s, w i * (t * S i ω + B i ω)) ^ 2 ∂μ) =
      t ^ 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * ∫ ω, S i ω * S j ω ∂μ) +
        t * ∑ i ∈ s, w i ^ 2 := by
  rw [integral_weighted_sum_sq s w (fun i ω => t * S i ω + B i ω)
    (fun i _ => ((hS i).const_mul t).add (hB i))]
  have hpair (i j : ι) := integral_observation_mul_observation
    (hS i) (hS j) (hB i) (hB j) (hSB i j) (hSB j i) (hzero i) (hzero j) t
  simp_rw [hpair, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [← integral_weighted_sum_sq s w B (fun i _ => hB i)]
    exact integral_weighted_noise_sq s w B hB hind hzero t hsecond

theorem centered_gaussian_moments {B : Ω → ℝ} {t : ℝ≥0}
    (hB : HasLaw B (gaussianReal 0 t) μ) :
    MemLp B 2 μ ∧ (∫ ω, B ω ∂μ) = 0 ∧ (∫ ω, B ω ^ 2 ∂μ) = t := by
  refine ⟨hB.hasGaussianLaw.memLp_two, ?_, ?_⟩
  · rw [hB.integral_eq, integral_id_gaussianReal]
  · have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := t)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable, integral_id_gaussianReal] at hv
    simp only [sub_zero] at hv
    simpa only [Function.comp_apply] using
      (hB.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans hv

theorem integral_weighted_gaussian_observation_sq [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (S B : ι → Ω → ℝ)
    (hS : ∀ i, MemLp (S i) 2 μ) {t : ℝ≥0}
    (hB : ∀ i, HasLaw (B i) (gaussianReal 0 t) μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hSB : ∀ i j, IndepFun (S i) (B j) μ) :
    (∫ ω, (∑ i ∈ s, w i * ((t : ℝ) * S i ω + B i ω)) ^ 2 ∂μ) =
      (t : ℝ) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * ∫ ω, S i ω * S j ω ∂μ) +
        (t : ℝ) * ∑ i ∈ s, w i ^ 2 :=
  integral_weighted_observation_sq s w S B
    hS (fun i => (centered_gaussian_moments (hB i)).1) hind hSB
    (fun i => (centered_gaussian_moments (hB i)).2.1) t
    (fun i => (centered_gaussian_moments (hB i)).2.2)

theorem critical_information_from_spin_sums [DecidableEq ι] [IsFiniteMeasure μ]
    (hm : m ≤ mΩ)
    {R : Ω → ℝ} (S B : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hS : ∀ i, MemLp (S i) 2 μ) {t : ℝ≥0} (ht : 0 < t)
    (hB : ∀ i, HasLaw (B i) (gaussianReal 0 t) μ)
    (hind : Pairwise (fun i j => IndepFun (B i) (B j) μ))
    (hSB : ∀ i j, IndepFun (S i) (B j) μ)
    (hRB : ∀ i, IndepFun R (B i) μ)
    (hadapted : ∀ i, StronglyMeasurable[m] (fun ω => (t : ℝ) * S i ω + B i ω))
    (s : ℕ → Finset ι) (w : ℕ → ι → ℝ)
    (hnorm : ∀ n, ∑ i ∈ s n, w n i ^ 2 = (n : ℝ) + 1)
    (hcorrelation : ∀ n, (∑ i ∈ s n, w n i * ∫ ω, R ω * S i ω ∂μ) = (n : ℝ) + 1)
    (henergy : ∀ n, (∑ i ∈ s n, ∑ j ∈ s n,
      w n i * w n j * ∫ ω, S i ω * S j ω ∂μ) ≤ ((n : ℝ) + 1) ^ 3) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤ ∫ ω, (μ[R | m] ω) ^ 2 ∂μ := by
  have hBm (i : ι) := centered_gaussian_moments (hB i)
  let Z : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ s n, w n i * ((t : ℝ) * S i ω + B i ω)
  apply critical_information_of_estimators hm hR Z
  · intro n
    exact memLp_weighted_sum (s n) (w n) _
      (fun i _ => ((hS i).const_mul (t : ℝ)).add (hBm i).1)
  · intro n
    exact Finset.stronglyMeasurable_fun_sum (s n)
      (f := fun i ω => w n i * ((t : ℝ) * S i ω + B i ω))
      (fun i _ => (stronglyMeasurable_const (b := w n i)).mul (hadapted i))
  · exact ht
  · intro n
    dsimp [Z]
    rw [integral_signal_mul_weighted_observation (s n) (w n) S B hR
      (fun i _ => hS i) (fun i _ => (hBm i).1) (fun i _ => hRB i)
      (fun i _ => (hBm i).2.1) (t : ℝ), hcorrelation n]
  · intro n
    dsimp [Z]
    rw [integral_weighted_gaussian_observation_sq (s n) (w n) S B hS hB hind hSB, hnorm n]
    have h := mul_le_mul_of_nonneg_left (henergy n) (sq_nonneg (t : ℝ))
    linarith

end Problem367

end OAI
