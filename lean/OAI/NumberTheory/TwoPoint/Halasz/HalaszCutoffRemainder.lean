import OAI.NumberTheory.TwoPoint.Halasz.HalaszHurwitzCutoff

namespace OAI

/-! The first-order cutoff has a bounded remainder when its length is
comparable with the square of the height. -/
namespace TwoPointCorrelations

open Complex

lemma halasz_cutoff_remainder {N E : ℝ} (hE : 1≤ E)
    (hNlo : E^2≤ N) (hNhi : N≤4*E^2) {s : ℂ}
    (hσ : 2/3≤ s.re) (hσhi : s.re≤2) (ht : |s.im|=E) :
    N^(1-s.re)/‖1-s‖+N^(-s.re)/2+2*‖s‖*N^(-s.re)/s.re≤15 := by
  have hE0 : 0<E := by linarith
  have hN : 1≤ N := by nlinarith
  have hN0 : 0<N := by linarith
  have hσ0 : 0<s.re := by linarith
  have hden : E≤‖1-s‖ := by
    have hh := Complex.abs_im_le_norm (1-s)
    simpa only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg,ht] using hh
  have hden0 : 0<‖1-s‖ := hE0.trans_le hden
  have hnorm : ‖s‖≤3*E := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hσ0.le,ht] at hh
    linarith
  have hrootlo : E≤ Real.sqrt N := (Real.le_sqrt hE0.le hN0.le).mpr hNlo
  have hroothi : Real.sqrt N≤2*E := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  have hneg : N^(-s.re)≤1/E := by
    calc
      _ ≤ N^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = 1/Real.sqrt N := by rw [Real.rpow_neg hN0.le,← Real.sqrt_eq_rpow]; simp only [one_div]
      _ ≤ _ := one_div_le_one_div_of_le hE0 hrootlo
  have hpos : N^(1-s.re)≤2*E := by
    calc
      _ ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
      _ ≤ _ := hroothi
  have hfirst : N^(1-s.re)/‖1-s‖≤2 := by
    apply (div_le_iff₀ hden0).mpr
    linarith
  have hsecond : N^(-s.re)/2≤1/2 := by
    have hh : 1/E≤1 := (div_le_one hE0).mpr hE
    linarith
  have hthird : 2*‖s‖*N^(-s.re)/s.re≤12 := by
    apply (div_le_iff₀ hσ0).mpr
    have hmul := mul_le_mul hnorm hneg (Real.rpow_nonneg hN0.le _) (by positivity : 0≤3*E)
    have heq : (3*E)*(1/E)=3 := by field_simp
    rw [heq] at hmul
    linarith
  linarith

end TwoPointCorrelations

end OAI
