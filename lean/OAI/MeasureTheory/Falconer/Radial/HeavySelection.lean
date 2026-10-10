import OAI.MeasureTheory.Falconer.Incidence.IncidenceMoment
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! # Counting heavy sets with small pairwise intersections

This second-moment estimate is the finite selection step for the published
heavy-hyperplane input. The geometric intersection estimate is kept separate.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators

theorem finite_indicator_square_integral {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    (∫⁻ x, (∑ i ∈ I, (A i).indicator (fun _ => (1:ℝ≥0∞)) x)^2 ∂μ) =
      ∑ i ∈ I, ∑ j ∈ I, μ (A i ∩ A j) := by
  classical
  have hpoint (x : X) : (∑ i ∈ I, (A i).indicator (fun _ => (1:ℝ≥0∞)) x)^2 =
      ∑ i ∈ I, ∑ j ∈ I, (A i ∩ A j).indicator (fun _ => (1:ℝ≥0∞)) x := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hi' : x ∈ A i <;> by_cases hj' : x ∈ A j <;> simp [hi',hj']
  simp_rw [hpoint]
  rw [lintegral_finsetSum' I (fun i hi =>
    (Finset.measurable_sum I fun j hj => measurable_const.indicator
      ((hA i hi).inter (hA j hj))).aemeasurable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum' I (fun j hj =>
    (measurable_const.indicator ((hA i hi).inter (hA j hj))).aemeasurable)]
  exact Finset.sum_congr rfl fun j hj => lintegral_indicator_one ((hA i hi).inter (hA j hj))

theorem heavy_pairwise_card_bound {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (I : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) {m : ℝ} (hm : 0 < m)
    (hheavy : ∀ i ∈ I, ENNReal.ofReal m ≤ μ (A i))
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → μ (A i ∩ A j) ≤ ENNReal.ofReal (m^2/2)) :
    (I.card:ℝ) ≤ 2/m := by
  classical
  let M : ℝ≥0∞ := ∑ i ∈ I, μ (A i)
  have hMfinite : M ≠ ∞ := by
    exact (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top μ (A i)).ne
  have hlow : (I.card:ℝ≥0∞)*ENNReal.ofReal m ≤ M := by
    simpa [M] using Finset.sum_le_sum hheavy
  have hlowR : (I.card:ℝ)*m ≤ M.toReal := by
    have h := ENNReal.toReal_mono hMfinite hlow
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hm.le] using h
  let F : X → ℝ≥0∞ := fun x => ∑ i ∈ I, (A i).indicator (fun _ => (1:ℝ≥0∞)) x
  have hF : Measurable F := Finset.measurable_sum I fun i hi =>
    measurable_const.indicator (hA i hi)
  have hFM : (∫⁻ x, F x ∂μ) = M := by
    rw [lintegral_finsetSum' I (fun i hi =>
      (measurable_const.indicator (hA i hi)).aemeasurable)]
    exact Finset.sum_congr rfl fun i hi => lintegral_indicator_one (hA i hi)
  have hsecond : M^2 ≤ ∑ i ∈ I, ∑ j ∈ I, μ (A i ∩ A j) := by
    have h := incidence_moment μ F hF.aemeasurable (by norm_num : 2 ≤ (2:ℕ))
    rw [hFM,measure_univ,one_pow,mul_one] at h
    exact h.trans_eq (finite_indicator_square_integral μ I A hA)
  have hupper : (∑ i ∈ I, ∑ j ∈ I, μ (A i ∩ A j)) ≤
      M+(I.card:ℝ≥0∞)^2*ENNReal.ofReal (m^2/2) := by
    calc
      _ ≤ ∑ i ∈ I, ∑ j ∈ I,
          ((if i=j then μ (A i) else 0)+ENNReal.ofReal (m^2/2)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i=j
        · subst j
          simp
        · simpa only [hij,ite_false,zero_add] using hpair i hi j hj hij
      _ = M+(I.card:ℝ≥0∞)^2*ENNReal.ofReal (m^2/2) := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
        simp [M,pow_two,mul_assoc]
  have hR : M.toReal^2 ≤ M.toReal+(I.card:ℝ)^2*(m^2/2) := by
    have ht : M+(I.card:ℝ≥0∞)^2*ENNReal.ofReal (m^2/2) ≠ ∞ := by finiteness
    have hh := ENNReal.toReal_mono ht (hsecond.trans hupper)
    rw [ENNReal.toReal_add hMfinite (by finiteness)] at hh
    simpa only [ENNReal.toReal_pow,
      ENNReal.toReal_mul,ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ m^2/2)] using hh
  have hsq : ((I.card:ℝ)*m)^2 ≤ M.toReal^2 :=
    (sq_le_sq₀ (by positivity) ENNReal.toReal_nonneg).mpr hlowR
  have hMle : M.toReal ≤ 2 := by nlinarith [ENNReal.toReal_nonneg (a := M)]
  exact (le_div_iff₀ hm).mpr (hlowR.trans hMle)

end Falconer

end OAI
