import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {ι : Type*}

lemma cosine_covariance_bounds (F : Finset ι) (w k : ι → ℝ)
    (tau B c : ℝ) (hw : ∀ i ∈ F, 0 ≤ w i)
    (htau : 0 ≤ tau) (hsmall : tau*B ≤ 1)
    (hk : ∀ i ∈ F, |k i| ≤ B)
    (hmoment : c ≤ ∑ i ∈ F, w i*(k i)^2) :
    (∑ i ∈ F, w i)/2 ≤ ∑ i ∈ F, w i*Real.cos (tau*k i) ∧
    (∑ i ∈ F, w i*Real.cos (tau*k i)) ≤
      (∑ i ∈ F, w i) - (2/Real.pi^2)*tau^2*c := by
  have ht (i : ι) (hi : i ∈ F) : |tau*k i| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg htau]
    exact (mul_le_mul_of_nonneg_left (hk i hi) htau).trans hsmall
  constructor
  · have hh := Finset.sum_le_sum (s := F) (fun i hi ↦
      mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ Real.cos (tau*k i) from by
        have hc := Real.one_sub_sq_div_two_le_cos (x := tau*k i)
        have hs := sq_le_sq.mpr (show |tau*k i| ≤ |(1:ℝ)| by simpa using ht i hi)
        nlinarith) (hw i hi))
    simpa only [← Finset.sum_mul,div_eq_mul_inv,one_mul] using hh
  · have hh := Finset.sum_le_sum (s := F) (fun i hi ↦
      mul_le_mul_of_nonneg_left (Real.cos_le_one_sub_mul_cos_sq
        ((ht i hi).trans (by linarith [Real.two_le_pi]))) (hw i hi))
    have he : (∑ i ∈ F, w i*(1-2/Real.pi^2*(tau*k i)^2)) =
        (∑ i ∈ F, w i) - (2/Real.pi^2)*tau^2*(∑ i ∈ F, w i*(k i)^2) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hh
    have hc : 0 ≤ (2/Real.pi^2)*tau^2 := by positivity
    exact hh.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left hmoment hc) _)

lemma cosine_covariance_coercive (F : Finset ι) (w k : ι → ℝ)
    (tau B c : ℝ) (hw : ∀ i ∈ F, 0 ≤ w i)
    (htau : 0 ≤ tau) (hsmall : tau*B ≤ 1)
    (hk : ∀ i ∈ F, |k i| ≤ B)
    (hmoment : c ≤ ∑ i ∈ F, w i*(k i)^2) (u v : ℝ) :
    (2/Real.pi^2)*tau^2*c*(u^2+v^2) ≤
      (∑ i ∈ F, w i)*(u^2+v^2) +
        2*(∑ i ∈ F, w i*Real.cos (tau*k i))*u*v := by
  obtain ⟨hlo,hhi⟩ := cosine_covariance_bounds F w k tau B c hw htau hsmall hk hmoment
  have hm : 0 ≤ ∑ i ∈ F, w i := Finset.sum_nonneg hw
  have hp : 0 ≤ (∑ i ∈ F, w i*Real.cos (tau*k i))*(u+v)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hq := mul_le_mul_of_nonneg_right hhi (add_nonneg (sq_nonneg u) (sq_nonneg v))
  nlinarith

lemma cosine_normalized_correlation (F : Finset ι) (w k : ι → ℝ)
    (tau B c : ℝ) (hw : ∀ i ∈ F, 0 ≤ w i)
    (htau : 0 ≤ tau) (hsmall : tau*B ≤ 1)
    (hk : ∀ i ∈ F, |k i| ≤ B)
    (hmoment : c ≤ ∑ i ∈ F, w i*(k i)^2)
    (hc : 0 ≤ c) (hm : 0 < ∑ i ∈ F, w i) (hm1 : ∑ i ∈ F, w i ≤ 1) :
    (1/2:ℝ) ≤ (∑ i ∈ F, w i*Real.cos (tau*k i))/(∑ i ∈ F, w i) ∧
    (∑ i ∈ F, w i*Real.cos (tau*k i))/(∑ i ∈ F, w i) ≤
      1-(2/Real.pi^2)*tau^2*c := by
  obtain ⟨hlo,hhi⟩ := cosine_covariance_bounds F w k tau B c hw htau hsmall hk hmoment
  constructor
  · apply (le_div_iff₀ hm).mpr
    linarith
  · apply (div_le_iff₀ hm).mpr
    have hd : 0 ≤ (2/Real.pi^2)*tau^2*c := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hm1 hd]

end
end Yau.Geometry

end OAI
