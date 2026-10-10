import Mathlib
import OAI.Probability.Perceptron.Variational.StepEntropy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma reciprocal_supporting_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y-x)/y^2 ≤ x⁻¹-y⁻¹ := by
  have he : x⁻¹-y⁻¹-(y-x)/y^2=(x-y)^2/(x*y^2) := by
    field_simp [hx.ne',hy.ne']
    ring
  have hp := div_nonneg (sq_nonneg (x-y)) (mul_pos hx (sq_pos_of_pos hy)).le
  rw [← he] at hp
  linarith

lemma max_difference_support {p q t : ℝ} :
    (if t ≤ q then p-q else 0) ≤ max p t-max q t := by
  split_ifs with ht
  · rw [max_eq_left ht]
    exact sub_le_sub_right (le_max_left _ _) _
  · rw [max_eq_right (le_of_not_ge ht)]
    exact sub_nonneg.mpr (le_max_right _ _)

theorem entropy_weightedStep_support {I : Type*} [Fintype I]
    (w : I → ℝ) (p q : I → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ i, (p i:ℝ) ≤ B) (hq : ∀ i, (q i:ℝ) ≤ B) :
    (∑ i, w i*((p i:ℝ)-(q i:ℝ))*weightedStepA w (fun j => (q j:ℝ)) (q i))/2 ≤
      (entropy (weightedStepTrial w p hw hw1)).toReal-
        (entropy (weightedStepTrial w q hw hw1)).toReal := by
  classical
  let P : I → ℝ := fun i => p i
  let Q : I → ℝ := fun i => q i
  let Dp := weightedStepTail w P
  let Dq := weightedStepTail w Q
  have hcP := weightedStepTail_inv_continuousOn w P hw hw1 hB1 hp
  have hcQ := weightedStepTail_inv_continuousOn w Q hw hw1 hB1 hq
  have hiP := hcP.intervalIntegrable_of_Icc (μ := volume) hB0
  have hiQ := hcQ.intervalIntegrable_of_Icc (μ := volume) hB0
  have hcQ2 : ContinuousOn (fun t => 1/(Dq t)^2) (Icc 0 B) := by
    have hh := hcQ.pow 2
    change ContinuousOn (fun t => ((Dq t)⁻¹)^2) _ at hh
    simpa only [one_div,inv_pow] using hh
  have hiQ2 := hcQ2.intervalIntegrable_of_Icc (μ := volume) hB0
  let F : I → ℝ → ℝ := fun i => (Iic (Q i)).indicator (fun t => 1/(Dq t)^2)
  have hFi (i : I) : IntervalIntegrable (F i) volume 0 B :=
    ⟨hiQ2.1.indicator measurableSet_Iic,hiQ2.2.indicator measurableSet_Iic⟩
  have hl (t : ℝ) (ht : t ∈ Icc 0 B) :
      (∑ i, w i*(P i-Q i)*F i t) ≤ (Dp t)⁻¹-(Dq t)⁻¹ := by
    have hDtP : 0 < Dp t := weightedStepTail_pos w P hw hw1 hB1 hp ht.2
    have hDtQ : 0 < Dq t := weightedStepTail_pos w Q hw hw1 hB1 hq ht.2
    have hmax : (∑ i, w i*(if t ≤ Q i then P i-Q i else 0)) ≤ Dq t-Dp t := by
      change _ ≤ (∑ i, w i*(1-max (Q i) t))-(∑ i, w i*(1-max (P i) t))
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have hm := mul_le_mul_of_nonneg_left (@max_difference_support (P i) (Q i) t) (hw i)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hmax (by positivity : 0 ≤ 1/(Dq t)^2)
    have he : (∑ i, w i*(P i-Q i)*F i t) =
        (∑ i, w i*(if t ≤ Q i then P i-Q i else 0))*(1/(Dq t)^2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [F,Set.indicator_apply,mem_Iic]
      split_ifs <;> ring
    rw [he]
    calc
      _ ≤ (Dq t-Dp t)*(1/(Dq t)^2) := hmul
      _ = (Dq t-Dp t)/(Dq t)^2 := by ring
      _ ≤ _ := reciprocal_supporting_inequality hDtP hDtQ
  have hiF : IntervalIntegrable (fun t => ∑ i, w i*(P i-Q i)*F i t) volume 0 B := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => (hFi i).const_mul (w i*(P i-Q i)))
    have he : (∑ i, fun t => w i*(P i-Q i)*F i t) =
        (fun t => ∑ i, w i*(P i-Q i)*F i t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  have hInt := intervalIntegral.integral_mono_on hB0 hiF (hiP.sub hiQ) hl
  have hIntF (i : I) : (∫ t in (0:ℝ)..B, F i t) = weightedStepA w Q (Q i) := by
    exact intervalIntegral.integral_indicator ⟨(q i).2.1,hq i⟩
  rw [intervalIntegral.integral_sub hiP hiQ,
    intervalIntegral.integral_finsetSum (fun i _ => (hFi i).const_mul _)] at hInt
  simp only [intervalIntegral.integral_const_mul,hIntF] at hInt
  rw [entropy_weightedStepTrial_toReal w p hw hw1 B hB0 hB1 hp,
    entropy_weightedStepTrial_toReal w q hw hw1 B hB0 hB1 hq]
  change (∑ i, w i*(P i-Q i)*weightedStepA w Q (Q i))/2 ≤
    ((∫ t in (0:ℝ)..B, (Dp t)⁻¹)+Real.log (1-B))/2-
      ((∫ t in (0:ℝ)..B, (Dq t)⁻¹)+Real.log (1-B))/2
  linarith

theorem stationary_finite_entropy_minimizes {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q p : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hp : Monotone p)
    (hq1 : (q (Fin.last k):ℝ) < 1) (hp1 : (p (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ) ≤
      (entropy (weightedStepTrial w p hw hw1)).toReal-∑ i, w i*h i*(p i:ℝ) := by
  let B := max (p (Fin.last k):ℝ) (q (Fin.last k):ℝ)
  have hB0 : 0 ≤ B := (p (Fin.last k)).2.1.trans (le_max_left _ _)
  have hB1 : B < 1 := max_lt hp1 hq1
  have hP (i : Fin (k+1)) : (p i:ℝ) ≤ B :=
    (show (p i:ℝ) ≤ (p (Fin.last k):ℝ) from hp (Fin.le_last i)).trans (le_max_left _ _)
  have hQ (i : Fin (k+1)) : (q i:ℝ) ≤ B :=
    (show (q i:ℝ) ≤ (q (Fin.last k):ℝ) from hq (Fin.le_last i)).trans (le_max_right _ _)
  have hs := entropy_weightedStep_support w p q hw hw1 B hB0 hB1 hP hQ
  have he : (∑ i, w i*((p i:ℝ)-(q i:ℝ))*weightedStepA w (fun j => (q j:ℝ)) (q i))/2 =
      (∑ i, w i*h i*(p i:ℝ))-(∑ i, w i*h i*(q i:ℝ)) := by
    rw [Finset.sum_div,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hstat i]
    ring
  rw [he] at hs
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
