import Mathlib
import OAI.Probability.SKGap.Localization.JumpEnergy
import OAI.Probability.SKGap.Localization.LinearObservable

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
namespace SKGapCutoff

lemma semigroup_abs_le_one {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t)
    {f : Observables n} (hf : ∀ x, |f x| ≤ 1) (x : Spin n) :
    |semigroup J t f x| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · have h := semigroup_mono J t ht (fun y => (abs_le.mp (hf y)).1) x
    simpa only [semigroup_const] using h
  · exact semigroup_le_const J t ht (fun y => (abs_le.mp (hf y)).2) x

lemma halfDiff_abs_le_one {n : ℕ} {f : Observables n}
    (hf : ∀ x, |f x| ≤ 1) (x : Spin n) (i : Fin n) : |halfDiff i f x| ≤ 1 := by
  have hp := abs_le.mp (hf (replace x i true))
  have hm := abs_le.mp (hf (replace x i false))
  unfold halfDiff
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma backward_energy_budget {n : ℕ} (J : Interaction n) {f : Observables n}
    (hf : ∀ x, |f x| ≤ 1) {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (x : Spin n) :
    (∫ s in a..T, semigroup J s (jumpEnergy J (semigroup J (T-s) f)) x) ≤ 1 := by
  have hT := ha.trans haT
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)]
      (fun s => semigroup J s (jumpEnergy J (semigroup J (T-s) f)) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact semigroup_nonneg J s hs.1.le _ (jumpEnergy_nonneg J _) x
  calc
    _ ≤ ∫ s in (0:ℝ)..T, semigroup J s (jumpEnergy J (semigroup J (T-s) f)) x :=
      intervalIntegral.integral_mono_interval ha haT le_rfl hnonneg
        ((interpolated_energy_continuous J f T x).intervalIntegrable 0 T)
    _ = semigroup J T (fun y => f y^2) x - (semigroup J T f x)^2 :=
      (semigroup_variance_integral J f T x).symm
    _ ≤ 1 := by
      have hb : semigroup J T (fun y => f y^2) x ≤ 1 := by
        apply semigroup_le_const J T hT
        intro y
        nlinarith [sq_abs (f y), hf y, abs_nonneg (f y)]
      nlinarith [sq_nonneg (semigroup J T f x)]

lemma gradient_le_energy_bad {n : ℕ} (J : Interaction n) {f : Observables n}
    (hf : ∀ x, |f x| ≤ 1) {w : ℝ} (hw : 0 < w)
    (bad : Spin n → Prop) [DecidablePred bad]
    (hgood : ∀ x, ¬bad x → ∀ i, w ≤ 1-mean J x i*spin x i) (x : Spin n) :
    (∑ i, (halfDiff i f x)^2) ≤ jumpEnergy J f x/(2*w) + (n:ℝ)*(if bad x then 1 else 0) := by
  by_cases hx : bad x
  · simp only [hx, ↓reduceIte, mul_one]
    have hb : (∑ i, (halfDiff i f x)^2) ≤ (n:ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [sq_abs (halfDiff i f x), halfDiff_abs_le_one hf x i,
            abs_nonneg (halfDiff i f x)]
        _ = _ := by simp
    exact hb.trans (le_add_of_nonneg_left (div_nonneg (jumpEnergy_nonneg J f x) (by positivity)))
  · simp only [hx, ↓reduceIte, mul_zero, add_zero]
    apply (le_div_iff₀ (by positivity : 0 < 2*w)).mpr
    unfold jumpEnergy
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hgood x hx i) (sq_nonneg (halfDiff i f x)))
    rw [← Finset.mul_sum] at hh
    nlinarith

lemma backward_gradient_energy_bound {n : ℕ} (J : Interaction n) {f : Observables n}
    (hf : ∀ x, |f x| ≤ 1) {s T w p : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hw : 0 < w)
    (bad : Spin n → Prop) [DecidablePred bad]
    (hgood : ∀ y, ¬bad y → ∀ i, w ≤ 1-mean J y i*spin y i)
    (x : Spin n) (hbad : semigroup J s (fun y => if bad y then 1 else 0) x ≤ p) :
    semigroup J s (fun y => ∑ i, (halfDiff i (semigroup J (T-s) f) y)^2) x ≤
      semigroup J s (jumpEnergy J (semigroup J (T-s) f)) x/(2*w) + (n:ℝ)*p := by
  have hf' := semigroup_abs_le_one J (sub_nonneg.mpr hsT) hf
  have hh := semigroup_mono J s hs (gradient_le_energy_bad J hf' hw bad hgood) x
  have he : (fun y => jumpEnergy J (semigroup J (T-s) f) y/(2*w)+(n:ℝ)*(if bad y then 1 else 0)) =
      (2*w)⁻¹ • jumpEnergy J (semigroup J (T-s) f) + (n:ℝ) • (fun y => if bad y then 1 else 0) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he, map_add, map_smul, map_smul] at hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
  calc
    _ ≤ (2*w)⁻¹ * semigroup J s (jumpEnergy J (semigroup J (T-s) f)) x +
        (n:ℝ)*semigroup J s (fun y => if bad y then 1 else 0) x := hh
    _ ≤ _ := by
      rw [div_eq_mul_inv, mul_comm _ (2*w)⁻¹]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg n))

lemma gradient_bound_from_backward_energy {n : ℕ} (J : Interaction n)
    {f : Observables n} (hf : ∀ x, |f x| ≤ 1) {a T w p K η : ℝ}
    (ha : 0 ≤ a) (haT : a < T) (hw : 0 < w) (hK : 0 ≤ K)
    (bad : Spin n → Prop) [DecidablePred bad]
    (hgood : ∀ y, ¬bad y → ∀ i, w ≤ 1-mean J y i*spin y i)
    (x : Spin n)
    (hbad : ∀ s ∈ Set.Icc a T, semigroup J s (fun y => if bad y then 1 else 0) x ≤ p)
    (hprop : ∀ s ∈ Set.Icc a T,
      (∑ i, (halfDiff i (semigroup J T f) x)^2) ≤
        K * semigroup J s (fun y => ∑ i, (halfDiff i (semigroup J (T-s) f) y)^2) x + η) :
    (∑ i, (halfDiff i (semigroup J T f) x)^2) ≤
      K * (1/(2*w*(T-a))+(n:ℝ)*p) + η := by
  let E : ℝ → ℝ := fun s => semigroup J s (jumpEnergy J (semigroup J (T-s) f)) x
  have hE : Continuous E := interpolated_energy_continuous J f T x
  have hbound : ∀ s ∈ Set.Icc a T,
      (∑ i, (halfDiff i (semigroup J T f) x)^2) ≤
        K/(2*w)*E s + (K*(n:ℝ)*p+η) := by
    intro s hs
    have hh := backward_gradient_energy_bound J hf (ha.trans hs.1) hs.2 hw bad hgood x (hbad s hs)
    have hh' := (hprop s hs).trans (add_le_add (mul_le_mul_of_nonneg_left hh hK) le_rfl)
    calc
      _ ≤ K*(E s/(2*w)+(n:ℝ)*p)+η := hh'
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) haT.le
    (intervalIntegrable_const (a := a) (b := T))
    ((hE.const_mul (K/(2*w))).add continuous_const |>.intervalIntegrable a T) hbound
  simp only [Pi.add_apply, intervalIntegral.integral_const, smul_eq_mul] at hi
  rw [intervalIntegral.integral_add ((hE.const_mul (K/(2*w))).intervalIntegrable a T)
      (intervalIntegrable_const (a := a) (b := T)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hi
  have hbudget : (∫ s in a..T, E s) ≤ 1 := backward_energy_budget J hf ha haT.le x
  have hKbudget := mul_le_mul_of_nonneg_left hbudget (div_nonneg hK (by positivity : 0 ≤ 2*w))
  have hfinal : (T-a)*(∑ i, (halfDiff i (semigroup J T f) x)^2) ≤
      K/(2*w)+(T-a)*(K*(n:ℝ)*p+η) := by linarith
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr haT)).mp
  calc
    _ = (T-a)*(∑ i, (halfDiff i (semigroup J T f) x)^2) := by ring
    _ ≤ K/(2*w)+(T-a)*(K*(n:ℝ)*p+η) := hfinal
    _ = _ := by field_simp [ne_of_gt hw, ne_of_gt (sub_pos.mpr haT)]; ring

lemma worstContinuous_le_of_backward_energy {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    {a T w p K η : ℝ} (ha : 0 ≤ a) (haT : a < T) (hw : 0 < w)
    (hp : 0 ≤ p) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (bad : Spin n → Prop) [DecidablePred bad]
    (hgood : ∀ y, ¬bad y → ∀ i, w ≤ 1-mean J y i*spin y i)
    (hbad : ∀ s ∈ Set.Icc a T, ∀ x,
      semigroup J s (fun y => if bad y then 1 else 0) x ≤ p)
    (hprop : ∀ f : Observables n, (∀ y, |f y| ≤ 1) → ∀ x, ∀ s ∈ Set.Icc a T,
      (∑ i, (halfDiff i (semigroup J T f) x)^2) ≤
        K * semigroup J s (fun y => ∑ i, (halfDiff i (semigroup J (T-s) f) y)^2) x + η) :
    worstContinuous J T ≤ Real.sqrt n * Real.sqrt (K*(1/(2*w*(T-a))+(n:ℝ)*p)+η) := by
  have hL : 0 ≤ K*(1/(2*w*(T-a))+(n:ℝ)*p)+η := by positivity
  apply worstContinuous_le_gradient J hJ hdiag T _ (Real.sqrt_nonneg _)
  intro f hf x
  rw [Real.sq_sqrt hL]
  exact gradient_bound_from_backward_energy J hf ha haT hw hK bad hgood x
    (fun s hs => hbad s hs x) (hprop f hf x)

end SKGapCutoff

open MeasureTheory Filter
open scoped BigOperators Topology

end

end OAI
