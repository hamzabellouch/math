import OAI.Combinatorics.GraphThreshold.Resampling
import OAI.Combinatorics.GraphThreshold.FiniteProbability
import OAI.Combinatorics.GraphThreshold.BernoulliCoupling

namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

attribute [local instance] Classical.propDecidable

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

def resamplingExperimentLaw (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    FiniteLaw (Finset X × (B × B)) where
  weight ω := bernoulliWeight ρ ω.1 * resamplingWeight ν A ρ ω.1 ω.2
  nonneg ω := mul_nonneg (bernoulliWeight_nonneg hρ.le hρ1 ω.1)
    (resamplingWeight_nonneg ν A hρ.le ω.1 ω.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, resamplingWeight_total ν A hν hρ, mul_one]
    exact bernoulliWeight_sum ρ

theorem resamplingExperiment_expectation (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (F : Finset X → B × B → ℝ) :
    (resamplingExperimentLaw ν A ρ hν hρ hρ1).expectation (fun ω => F ω.1 ω.2) =
      bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).expectation (F W)) := by
  simp only [FiniteLaw.expectation, resamplingExperimentLaw, Fintype.sum_prod_type,
    bernoulliExpectation, resamplingLaw_weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  apply Finset.sum_congr rfl
  intro cb _
  ring_nf

/-- Mixture expansion before using the Bernoulli union identity. -/
theorem bernoulliExpectation_resampling_source (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => ν.expectation (fun c => F (resamplingY A W c))) =
      ∑ c, ν.weight c * bernoulliExpectation ρ (fun W => F (W ∪ A c)) := by
  simp only [bernoulliExpectation, FiniteLaw.expectation, resamplingY, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro W _
  ring_nf

/-- Expand the proposed density into the finite mixture of conditional
Bernoulli densities. This is an algebraic identity, not a normalization premise. -/
theorem bernoulliExpectation_resamplingZ (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) =
      ∑ c, ν.weight c * bernoulliExpectation ρ
        (fun Y => if A c ⊆ Y then F Y / ρ ^ (A c).card else 0) := by
  classical
  simp only [bernoulliExpectation, resamplingZ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hY : A c ⊆ Y
  · simp only [resamplingNumerator, ite_eq_left hY, div_eq_mul_inv, inv_pow]
    ring_nf
  · simp only [resamplingNumerator, ite_eq_right hY, zero_mul, mul_zero]

theorem resampling_source_density (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : ρ ≠ 0) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => ν.expectation (fun c => F (resamplingY A W c))) =
      bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) := by
  rw [bernoulliExpectation_resampling_source, bernoulliExpectation_resamplingZ]
  apply Finset.sum_congr rfl
  intro c _
  rw [bernoulliExpectation_union_fixed ρ hρ]

theorem resampling_density (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).expectation
      (fun cb => F (resamplingY A W cb.1))) =
      bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) := by
  calc
    _ = bernoulliExpectation ρ (fun W => ν.expectation
        (fun c => F (resamplingY A W c))) := by
      unfold bernoulliExpectation
      apply Finset.sum_congr rfl
      intro W _
      exact congrArg (fun x => bernoulliWeight ρ W * x)
        (resampling_expectation_source ν A hν hρ W (fun c => F (resamplingY A W c)))
    _ = _ := resampling_source_density ν A hρ.ne' F

/-- Event form of the observed-set density formula, used for small-`Z`
failure events in the actual resampling procedure. -/
theorem resampling_density_prob (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (P : Finset X → Prop) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => P (resamplingY A W cb.1))) =
      bernoulliExpectation ρ (fun Y => if P Y then resamplingZ ν A ρ Y else 0) := by
  classical
  simpa only [FiniteLaw.prob_eq_expectation, mul_ite, mul_one, mul_zero] using
    resampling_density ν A hν hρ (fun Y => if P Y then 1 else 0)

theorem resamplingExperiment_density (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (F : Finset X → ℝ) :
    (resamplingExperimentLaw ν A ρ hν hρ hρ1).expectation
      (fun ω => F (resamplingY A ω.1 ω.2.1)) =
      bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) := by
  exact (resamplingExperiment_expectation ν A hν hρ hρ1
    (fun W cb => F (resamplingY A W cb.1))).trans (resampling_density ν A hν hρ F)

theorem resamplingExperiment_density_prob (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Finset X → Prop) :
    (resamplingExperimentLaw ν A ρ hν hρ hρ1).prob
      (fun ω => P (resamplingY A ω.1 ω.2.1)) =
      bernoulliExpectation ρ (fun Y => if P Y then resamplingZ ν A ρ Y else 0) := by
  classical
  simpa only [FiniteLaw.prob_eq_expectation, mul_ite, mul_one, mul_zero] using
    resamplingExperiment_density ν A hν hρ hρ1 (fun Y => if P Y then 1 else 0)

/-- Every atom of the observed-set law is exactly the Bernoulli atom times
the explicit finite density `Z`. -/
theorem resamplingExperiment_observed_mass (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (Y : Finset X) :
    (resamplingExperimentLaw ν A ρ hν hρ hρ1).prob
      (fun ω => resamplingY A ω.1 ω.2.1 = Y) =
      bernoulliWeight ρ Y * resamplingZ ν A ρ Y := by
  classical
  simpa [bernoulliExpectation, mul_ite] using
    resamplingExperiment_density_prob ν A hν hρ hρ1 (fun Y' => Y' = Y)

end LeanBlast.SecondKahnKalai

end

end OAI
