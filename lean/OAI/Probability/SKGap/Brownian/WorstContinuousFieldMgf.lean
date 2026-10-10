import Mathlib
import OAI.Probability.SKGap.Localization.ExpDrift
import OAI.Probability.SKGap.Localization.SemigroupAbs
import OAI.Probability.SKGap.Localization.ExpAbsSum

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
namespace SKGapCutoff

lemma worstContinuous_le_of_field_mgf {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    {a T H θ m C K η : ℝ} (ha : 0 ≤ a) (haT : a < T) (hθ : 0 ≤ θ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hmean : ∀ s ∈ Set.Icc a T, ∀ x i, |semigroup J s (fun y => field J y i) x| ≤ m)
    (hmgf : ∀ s ∈ Set.Icc a T, ∀ x i, ∀ σ ∈ ({-1,1}:Set ℝ),
      semigroup J s (fun y => Real.exp (σ*θ*(field J y i -
        semigroup J s (fun z => field J z i) x))) x ≤ C)
    (hprop : ∀ f : Observables n, (∀ y, |f y| ≤ 1) → ∀ x, ∀ s ∈ Set.Icc a T,
      (∑ i, (halfDiff i (semigroup J T f) x)^2) ≤
        K * semigroup J s (fun y => ∑ i, (halfDiff i (semigroup J (T-s) f) y)^2) x + η) :
    worstContinuous J T ≤ Real.sqrt n * Real.sqrt
      (K*((1+Real.exp (2*H))/(4*(T-a)) +
        2*(n:ℝ)^2*C*Real.exp (-θ*(H-m)))+η) := by
  classical
  let bad : Spin n → Prop := fun y => ∃ i, H < |field J y i|
  have hgood : ∀ y, ¬bad y → ∀ i, 2/(1+Real.exp (2*H)) ≤ 1-mean J y i*spin y i := by
    intro y hy i
    exact jumpWeight_lower_from_field J y i (le_of_not_gt (fun hi => hy ⟨i, hi⟩))
  have hb : ∀ s ∈ Set.Icc a T, ∀ x,
      semigroup J s (fun y => if bad y then 1 else 0) x ≤
        2*(n:ℝ)*C*Real.exp (-θ*(H-m)) := by
    intro s hs x
    exact semigroup_max_tail J (fun i y => field J y i) (ha.trans hs.1) hθ x
      (hmean s hs x) (hmgf s hs x)
  have hh := worstContinuous_le_of_backward_energy J hJ hdiag ha haT
    (by positivity : 0 < 2/(1+Real.exp (2*H))) (by positivity : 0 ≤ 2*(n:ℝ)*C*Real.exp (-θ*(H-m)))
    hK hη bad hgood hb hprop
  have he : K*(1/(2*(2/(1+Real.exp (2*H)))*(T-a))+
      (n:ℝ)*(2*(n:ℝ)*C*Real.exp (-θ*(H-m))))+η =
      K*((1+Real.exp (2*H))/(4*(T-a)) + 2*(n:ℝ)^2*C*Real.exp (-θ*(H-m)))+η := by
    field_simp [ne_of_gt (sub_pos.mpr haT), ne_of_gt (show 0 < 1+Real.exp (2*H) by positivity)]
    ; ring
  rw [he] at hh
  exact hh

lemma abs_gibbsExpectation_le {n : ℕ} (J : Interaction n) (f : Observables n) :
    |gibbsExpectation J f| ≤ gibbsExpectation J (fun x => |f x|) := by
  unfold gibbsExpectation
  simpa only [abs_mul, abs_of_pos (gibbs_pos J _)] using Finset.abs_sum_le_sum_abs
    (s := Finset.univ) (f := fun x => gibbs J x*f x)

lemma semigroup_abs_centered_le_gradient {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f : Observables n) (hcenter : gibbsExpectation J f = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hgrad : ∀ y, ∑ i, (halfDiff i (semigroup J t f) y)^2 ≤ C^2) (x : Spin n) :
    |semigroup J t f x| ≤ 2*Real.sqrt n*C := by
  have he : semigroup J t f x =
      gibbsExpectation J (fun y => semigroup J t f x-semigroup J t f y) := by
    rw [gibbsExpectation_sub, gibbsExpectation_const, gibbsExpectation_semigroup J hJ hdiag t f,
      hcenter, sub_zero]
  rw [he]
  apply (abs_gibbsExpectation_le J _).trans
  calc
    _ ≤ gibbsExpectation J (fun _ => 2*Real.sqrt n*C) := by
      apply gibbsExpectation_mono
      intro y
      exact euclidean_oscillation _ C hC hgrad x y
    _ = _ := gibbsExpectation_const J _

lemma field_gibbs_centered {n : ℕ} (J : Interaction n) (i : Fin n) :
    gibbsExpectation J (fun y => field J y i) = 0 :=
  linearObservable_centered J (J i)

lemma exponential_envelope_integral {C ρ η T : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) :
    (∫ r in (0:ℝ)..T, C*Real.exp (-2*ρ*r)+η) ≤ C/(2*ρ)+η*T := by
  have hcont : Continuous (fun r : ℝ => C*Real.exp (-2*ρ*r)) := by fun_prop
  rw [intervalIntegral.integral_add (hcont.intervalIntegrable 0 T) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_comp_mul_left Real.exp (mul_ne_zero (by norm_num) hρ.ne'), integral_exp]
  simp only [mul_zero, Real.exp_zero, sub_zero, smul_eq_mul]
  calc
    _ = C/(2*ρ)*(1-Real.exp (-2*ρ*T))+η*T := by
      field_simp
      ring
    _ ≤ _ := by
      have hh := mul_nonneg (div_nonneg hC (by positivity : 0 ≤ 2*ρ)) (Real.exp_pos (-2*ρ*T)).le
      nlinarith

lemma exponential_envelope_mgf {n : ℕ} (J : Interaction n) (f : Observables n)
    {T C ρ η θ : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hgrad : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ y,
      (∑ i, (halfDiff i (semigroup J r f) y)^2) ≤ C*Real.exp (-2*ρ*r)+η)
    (x : Spin n) :
    semigroup J T (fun y => Real.exp (θ*(f y-semigroup J T f x))) x ≤
      Real.exp (2*θ^2*Real.exp (2*|θ| *Real.sqrt (C+η))*(C/(2*ρ)+η*T)) := by
  have hcont : Continuous (fun r : ℝ => C*Real.exp (-2*ρ*r)+η) := by fun_prop
  apply (semigroup_jump_mgf J f T hT _ (C+η) θ (hcont.intervalIntegrable 0 T) ?_ hgrad x).trans
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (exponential_envelope_integral hC hρ) (by positivity)
  · intro r hr
    have he : Real.exp (-2*ρ*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.1])
    nlinarith

end SKGapCutoff

open MeasureTheory Filter
open scoped BigOperators Topology

end

end OAI
