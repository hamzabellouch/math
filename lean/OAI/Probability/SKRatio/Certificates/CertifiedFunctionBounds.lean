import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedFunctions

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

lemma abs_v_le (h : ℝ) : |v h| ≤ 1 := by rw [abs_of_pos (v_pos h)]; exact v_le_one h
lemma abs_m_le (h : ℝ) : |m h| ≤ 1 := (abs_lt.mpr (m_bounds h)).le
lemma abs_mv_le (h : ℝ) : |m h*v h| ≤ 1 := by
  rw [abs_mul]
  nlinarith [mul_le_mul (abs_m_le h) (abs_v_le h) (abs_nonneg (v h)) (by norm_num : (0:ℝ) ≤ 1)]

lemma approx_coefficient_bound {β A : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) : |1/2-β^2*A/(64/100-(19/100)*A)| ≤ 1 := by
  have hd : 0 < 64/100-(19/100)*A := by linarith
  have hp : 0 ≤ β^2*A/(64/100-(19/100)*A) := by positivity
  have hu : β^2*A/(64/100-(19/100)*A) ≤ 3/2 := by
    apply (div_le_iff₀ hd).mpr
    have hh : β^2 ≤ (1/4:ℝ) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hh hA
    nlinarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma approxF_bound {β A C Q : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1) (x : ℝ) :
    |approxF β A C (β^2+β*x)-Q| ≤ |x|+4 := by
  let h := β^2+β*x
  have hh : |h| ≤ 1/4+|x|/2 := by
    have ht := abs_add_le (β^2) (β*x)
    rw [abs_of_nonneg (sq_nonneg β),abs_mul,abs_of_nonneg hβ] at ht
    have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
    dsimp [h]
    nlinarith
  have hp : |(v h+A)*h| ≤ 2*|h| := by
    rw [abs_mul,abs_of_nonneg (by positivity [v_pos h] : 0 ≤ v h+A)]
    exact mul_le_mul_of_nonneg_right (by linarith [v_le_one h]) (abs_nonneg h)
  have h2 : |2*β^2*(m h*v h)| ≤ 1/2 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*β^2)]
    have ht := mul_le_mul_of_nonneg_left (abs_mv_le h) (by positivity : 0 ≤ 2*β^2)
    nlinarith
  have h3 : |(1/2-β^2*A/(64/100-(19/100)*A))*v h| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (approx_coefficient_bound hβ hb hA hA1) (abs_v_le h)
      (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h4 : |(12/100:ℝ)*m h| ≤ 12/100 := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 12/100)]
    nlinarith [abs_m_le h]
  have h5 : |3*β^2*C*g h| ≤ 3/4 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 3*β^2*C)]
    have ht := mul_le_mul_of_nonneg_left (abs_g_le_one h) (by positivity : 0 ≤ 3*β^2*C)
    have hh' := mul_le_mul_of_nonneg_left hC1 (by positivity : 0 ≤ 3*β^2)
    nlinarith
  have hsum : |approxF β A C h-Q| ≤ 2*|h|+237/100+Q := by
    unfold approxF
    calc
      _ ≤ |(v h+A)*h+2*β^2*(m h*v h)+(1/2-β^2*A/(64/100-(19/100)*A))*v h+
        (12/100)*m h+3*β^2*C*g h|+|Q| := abs_sub _ _
      _ ≤ ((((|(v h+A)*h|+|2*β^2*(m h*v h)|)+|(1/2-β^2*A/(64/100-(19/100)*A))*v h|)+
        |(12/100)*m h|)+|3*β^2*C*g h|)+|Q| := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add
              ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ _ := by rw [abs_of_nonneg hQ]; linarith only [hp,h2,h3,h4,h5]
  change |approxF β A C h-Q| ≤ _
  linarith only [hsum,hh,hQ1]

lemma bounded_center_square {u c : ℝ} (hu : |u| ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    |(u-c)^2| ≤ 4 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := abs_sub u c
  rw [abs_of_nonneg hc] at h
  have hh : |u-c| ≤ 2 := by linarith
  simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using (sq_le_sq₀ (abs_nonneg (u-c)) (by norm_num : (0:ℝ) ≤ 2)).mpr hh

lemma scalarFunction_bound {β A C M Q : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1/2)
    (hA : 0 ≤ A) (hA1 : A ≤ 1) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (k : ℕ) (x : ℝ) : |scalarFunction β A C M Q k (β^2+β*x)| ≤ 32*(1+x^2) := by
  let h := β^2+β*x
  have ht : (4:ℝ) ≤ 32*(1+x^2) := by nlinarith [sq_nonneg x]
  have hv := v_le_one h
  have hv0 := (v_pos h).le
  have hL := multiplier_pos h
  have hL0 := multiplier_strict_pos h
  have hm := m_bounds h
  have hd : 0 < 2-m h := by linarith
  have hd1 : 1 ≤ 2-m h := by linarith
  have hv2 : v h^2 ≤ 1 := by nlinarith
  have hs : |(approxF β A C h-Q)^2| ≤ 32*(1+x^2) := by
    have hh := approxF_bound hβ hb hA hA1 hC hC1 hQ hQ1 x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ |x|+4)).mpr hh
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (|x|-1),sq_abs x]
  unfold scalarFunction
  split
  · exact (abs_v_le h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · exact (abs_g_le_one h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · exact (abs_mv_le h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · rw [abs_of_nonneg (rho_nonneg h)]
    exact (rho_le_one h).trans ((by norm_num : (1:ℝ) ≤ 4).trans ht)
  · exact (bounded_center_square (abs_v_le h) hA hA1).trans ht
  · exact (bounded_center_square (abs_g_le_one h) hC hC1).trans ht
  · exact (bounded_center_square (abs_mv_le h) hM hM1).trans ht
  · exact hs
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ (1+v h)^2/multiplier h/16)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ v h^2/multiplier h/16)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ v h^2/(2-m h)/4)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply le_trans _ ht
    rw [abs_of_nonneg (by positivity : 0 ≤ v h^2/(2-m h)^2/4)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  · apply le_trans _ ht
    have hm' : 0 ≤ 1+m h := by linarith
    rw [abs_of_nonneg (by positivity : 0 ≤ v h*(1+m h)/4)]
    have ht' := mul_le_mul hv (show 1+m h ≤ 2 by linarith) hm' (by norm_num : (0:ℝ) ≤ 1)
    nlinarith

end SKRatio.Certificate

end

end OAI
