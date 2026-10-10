import OAI.NumberTheory.Ostmann.Construction.FiniteStatistic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def FinitePrior.fromWeights {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hZ : 0 < ∑ i, w i) : FinitePrior ι where
  mass i := w i/(∑ j, w j)
  mass_nonneg i := div_nonneg (hw i) hZ.le
  mass_total := by rw [← Finset.sum_div, div_self hZ.ne']

theorem FinitePrior.fromWeights_mean {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hZ : 0 < ∑ i, w i) (f : ι → ℝ) :
    (FinitePrior.fromWeights w hw hZ).mean f = (∑ i, w i*f i)/(∑ i, w i) := by
  simp only [FinitePrior.mean, FinitePrior.fromWeights, div_mul_eq_mul_div, Finset.sum_div]

theorem exists_positive_weight_mean {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hZ : 0 < ∑ i, w i) {a : ℝ}
    (hmean : a*(∑ i, w i) ≤ ∑ i, w i*f i) :
    ∃ i, 0 < w i ∧ a ≤ f i := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, 0 < w j := by
    by_contra h
    push Not at h
    have hsum : (∑ j, w j) ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
    linarith
  by_contra h
  push Not at h
  have hle (i : ι) : w i*f i ≤ w i*a := by
    by_cases hi : w i=0
    · simp only [hi, zero_mul, le_refl]
    · exact (mul_lt_mul_of_pos_left (h i (lt_of_le_of_ne (hw i) (Ne.symm hi)))
        (lt_of_le_of_ne (hw i) (Ne.symm hi))).le
  have hstrict : (∑ i, w i*f i) < ∑ i, w i*a :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (h j hj) hj⟩
  rw [← Finset.sum_mul] at hstrict
  nlinarith

theorem empirical_error_sq_le {ι : Type*} [Fintype ι]
    (e F : ι → ℝ) {P : ℝ} (hP : (∑ x, (F x)^2) ≤ P) :
    (∑ x, e x*F x)^2 ≤ P*(∑ x, (e x)^2) := by
  calc
    _ ≤ (∑ x, (e x)^2)*(∑ x, (F x)^2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e F
    _ ≤ (∑ x, (e x)^2)*P := mul_le_mul_of_nonneg_left hP
      (Finset.sum_nonneg (fun x _ => sq_nonneg _))
    _ = _ := mul_comm _ _

theorem weighted_error_sq_le {ι : Type*} [Fintype ι]
    (w e : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i*|e i|)^2 ≤ (∑ i, w i)*(∑ i, w i*(e i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i)*|e i|)
  have hfirst (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*|e i|) = w i*|e i| := by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have hsecond (i : ι) : (Real.sqrt (w i)*|e i|)^2 = w i*(e i)^2 := by
    rw [mul_pow, Real.sq_sqrt (hw i), sq_abs]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw _)] using h

end Ostmann.Construction

end

end OAI
