import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianDensityError
import OAI.Computability.MinUncut.Estimates.ConditionalRounding

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace MinUncut.FiniteGaussian
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

lemma smallBall_indicator_integrable (v : ι → ℝ) (r : ℝ) :
    Integrable ({x : ι → ℝ | |score v x| ≤ r}.indicator (fun _ => (1:ℝ))) (gaussianLaw ι) := by
  apply (integrable_const (1:ℝ)).indicator
  apply measurableSet_le _ measurable_const
  unfold score
  fun_prop

lemma setIntegral_tableTest_rounding (v : S → ι → ℝ) (hv : ∀ s, 1 ≤ ‖vector (v s)‖^2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ s, (∑ i, |v s i|) ≤ A)
    {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    (∫ x in cube T, |F (thresholdTable v x)-
      gridStep T L (fun j => F (thresholdTable v (gridPoint T L j))) x| ∂gaussianLaw ι) ≤
      2*(Fintype.card S)*A*((T:ℝ)/L) := by
  let B (s : S) := {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ))
  have hB (s : S) : Integrable (B s) (gaussianLaw ι) := smallBall_indicator_integrable _ _
  have hi := ((tableTest_integrable v F hF).sub (gridStep_integrable T L
    (fun j => F (thresholdTable v (gridPoint T L j))))).abs
  have hnonneg (x : ι → ℝ) : 0 ≤ ∑ s, B s x :=
    Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  calc
    _ ≤ ∫ x in cube T, ∑ s, B s x ∂gaussianLaw ι :=
      setIntegral_mono_on hi.integrableOn (integrable_finsetSum _ (fun s _ => hB s)).integrableOn
        (cube_measurable T) (fun x hx => tableTest_rounding_pointwise v hA hT hL F hF hx)
    _ ≤ ∫ x, ∑ s, B s x ∂gaussianLaw ι :=
      setIntegral_le_integral (integrable_finsetSum _ (fun s _ => hB s)) (Filter.Eventually.of_forall hnonneg)
    _ = ∑ s, (gaussianLaw ι).real {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)} := by
      rw [integral_finsetSum _ (fun s _ => hB s)]
      apply Finset.sum_congr rfl
      intro s _
      rw [show B s={x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) by rfl,
        integral_indicator (measurableSet_le (by unfold score; fun_prop) measurable_const),
        setIntegral_const,smul_eq_mul,mul_one]
    _ ≤ ∑ _ : S, 2*(A*((T:ℝ)/L)) :=
      Finset.sum_le_sum (fun s _ => score_small_ball (hv s) (by positivity))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma conditional_tableTest_bound (v : S → ι → ℝ) (hv : ∀ s, 1 ≤ ‖vector (v s)‖^2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ s, (∑ i, |v s i|) ≤ A)
    {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    |(∫ x, F (thresholdTable v x) ∂gaussianLaw ι)-
      (∫ x in cube T, gridStep T L (fun j => F (thresholdTable v (gridPoint T L j))) x ∂gaussianLaw ι)/
        (gaussianLaw ι).real (cube T)| ≤
      (Fintype.card ι:ℝ)/(T:ℝ)^2+2*(Fintype.card S)*A*((T:ℝ)/L) := by
  have h := conditional_rounding_bound (cube_measurable T) (gaussian_cube_pos hT)
    (tableTest_integrable v F hF) (gridStep_integrable T L _)
    (fun x => hF (thresholdTable v x))
    (gridStep_range hT.le hL _ (fun j => hF (thresholdTable v (gridPoint T L j))))
  exact h.trans (add_le_add (gaussian_cube_tail hT)
    (setIntegral_tableTest_rounding v hv hA0 hA hT.le hL F hF))

end MinUncut.FiniteGaussian

end
end

end OAI
