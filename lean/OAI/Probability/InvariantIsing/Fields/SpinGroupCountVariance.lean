import OAI.Probability.InvariantIsing.Fields.SpinGroupProjectionMoment
import Mathlib.Probability.Moments.Variance

namespace OAI

/-! Count fluctuations under the independent canonical site law. The
result applies to the averaged Gaussian spin kernels as soon as their
bias equations give the prescribed group means. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace InvariantIsing

def spinGroupCountSummand {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (i : Fin N) (b : Bool) : ℝ :=
  if group i = a ∧ b = true then 1 else 0

lemma sum_spinGroupCountSummand {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (σ : Spin N) :
    (∑ i, spinGroupCountSummand group a i (σ i)) = spinGroupCount group σ a := by
  simp [spinGroupCountSummand, spinGroupCount]

lemma spinGroupCountSummand_memLp {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (i : Fin N) (μ : Measure Bool) [IsFiniteMeasure μ] :
    MemLp (spinGroupCountSummand group a i) 2 μ := by
  apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
  apply ae_of_all
  intro b
  simp only [spinGroupCountSummand]
  split_ifs <;> norm_num

lemma variance_spinGroupCountSummand_le {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (i : Fin N) (μ : Measure Bool) [IsProbabilityMeasure μ] :
    Var[spinGroupCountSummand group a i; μ] ≤ if group i = a then (1 : ℝ) else 0 := by
  rw [variance_eq_sub (spinGroupCountSummand_memLp group a i μ)]
  have hi : (∫ b, (spinGroupCountSummand group a i b) ^ 2 ∂μ) ≤
      if group i = a then (1 : ℝ) else 0 := by
    calc
      _ ≤ ∫ _b, (if group i = a then (1 : ℝ) else 0) ∂μ :=
        integral_mono Integrable.of_finite (integrable_const _) (fun b => by
          by_cases hg : group i = a <;> cases b <;> simp [spinGroupCountSummand, hg])
      _ = _ := by
        have hu : μ.real Set.univ = 1 := by rw [measureReal_def, measure_univ]; norm_num
        simp only [integral_const, hu, one_smul]
  change (∫ b, (spinGroupCountSummand group a i b) ^ 2 ∂μ) - _ ≤ _
  linarith [sq_nonneg (∫ b, spinGroupCountSummand group a i b ∂μ)]

theorem spinGroupCount_variance_le {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] :
    Var[fun σ : Spin N => (spinGroupCount group σ a : ℝ); Measure.pi μ] ≤
      spinGroupSize group a := by
  have hf : (fun σ : Spin N => (spinGroupCount group σ a : ℝ)) =
      ∑ i, fun σ : Spin N => spinGroupCountSummand group a i (σ i) := by
    funext σ
    simp only [Finset.sum_apply, sum_spinGroupCountSummand]
  rw [hf, variance_sum_pi (fun i => spinGroupCountSummand_memLp group a i (μ i))]
  calc
    _ ≤ ∑ i, if group i = a then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => variance_spinGroupCountSummand_le group a i (μ i))
    _ = _ := by simp [spinGroupSize]

theorem spinGroupCount_centered_sq_le {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (k : ℕ)
    (hmean : (∫ σ : Spin N, (spinGroupCount group σ a : ℝ) ∂Measure.pi μ) = k) :
    (∫ σ : Spin N, ((spinGroupCount group σ a : ℝ) - k) ^ 2 ∂Measure.pi μ) ≤
      spinGroupSize group a := by
  have hv := spinGroupCount_variance_le group a μ
  rw [variance_eq_integral (measurable_of_finite _).aemeasurable, hmean] at hv
  exact hv

theorem spinGroupProjection_product_mean_distance {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hmean : ∀ a, (∫ σ : Spin N, (spinGroupCount group σ a : ℝ) ∂Measure.pi μ) = k a) :
    (∫ σ : Spin N, (hammingDist σ (spinGroupProjection group k hk σ) : ℝ) ∂Measure.pi μ) ≤
      ∑ a, Real.sqrt (spinGroupSize group a) := by
  simp_rw [spinGroupProjection_distance_real]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_le_sum
  intro a _
  exact (finite_integral_abs_le_sqrt_sq (Measure.pi μ)
    (fun σ : Spin N => (spinGroupCount group σ a : ℝ) - k a)).trans
      (Real.sqrt_le_sqrt (spinGroupCount_centered_sq_le group a μ (k a) (hmean a)))

end InvariantIsing

end

end OAI
