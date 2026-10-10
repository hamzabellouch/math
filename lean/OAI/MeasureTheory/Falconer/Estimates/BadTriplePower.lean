import OAI.MeasureTheory.Falconer.Slicing.GaussianBadTripleMass
import OAI.MeasureTheory.Falconer.Radial.EndpointRadialLosses

namespace OAI

/-! # A fixed power bound for the original bad-triple Gaussian average -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma bad_triple_distance_factor {R b C : ℝ} (hR : 0 < R) (h : ℕ) :
    (C/(R^(-b)/4)^2)^h = (16*C)^h*R^(2*(h:ℝ)*b) := by
  have he : C/(R^(-b)/4)^2 = (16*C)*R^(2*b) := by
    rw [div_pow,Real.rpow_neg hR.le]
    have hpow : (R^b)^2 = R^(2*b) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
      congr 1
      ring
    rw [← hpow]
    field_simp
    ring
  rw [he,mul_pow,← Real.rpow_natCast (R^(2*b)) h,← Real.rpow_mul hR.le]
  congr 2
  ring

theorem bad_triple_power_budget (h H : ℕ) (hH : 0 < H) {ell a b e : ℝ}
    (_hb : 0 < b) (hell : (h:ℝ) < ell)
    (hscale : 1/(H:ℝ) < a-2*b)
    (hgap : 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      8*(2*((2:ℝ)^N)^(-a))/(((2:ℝ)^N)^(-b))^2 ≤ 1/(2:ℝ)^(N/H) ∧
      ENNReal.ofReal ((gaussianTripleBandConstant/((((2:ℝ)^N)^(-b))/4)^2)^h) *
        ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*((2:ℝ)^N)^e*(3:ℝ)^ell)*
          (((2:ℝ)^(N/H))^((h:ℝ)-ell))*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ell))))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  let q := (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e
  let D := (16*gaussianTripleBandConstant)^h*(2:ℝ)^(h:ℝ)*
    (2*(3:ℝ)^ell)*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ell)))
  obtain ⟨Ns,hs⟩ := Regularization.fixed_constant_absorbed (sub_pos.mpr hscale) (16:ℝ)
  obtain ⟨Nc,hc⟩ := Regularization.fixed_constant_absorbed (half_pos hgap) D
  refine ⟨q/2,half_pos hgap,2*H+Ns+Nc,?_⟩
  intro N hN
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hNh : 2*H ≤ N := by omega
  have hscale' : 16*R^(-(a-2*b)) ≤ R^(-(1/(H:ℝ))) := by
    calc
      _ ≤ R^(a-2*b-1/(H:ℝ))*R^(-(a-2*b)) :=
        mul_le_mul_of_nonneg_right (hs N (by omega)) (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  constructor
  · have he : 8*(2*R^(-a))/(R^(-b))^2 = 16*R^(-(a-2*b)) := by
      rw [← Real.rpow_natCast (R^(-b)) 2,← Real.rpow_mul hR.le]
      calc
        _ = 16*(R^(-a)*R^(-(-b*(2:ℝ)))) := by
          rw [div_eq_mul_inv,← Real.rpow_neg hR.le]
          ring_nf
        _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring_nf
    rw [he]
    apply hscale'.trans
    have hdiv : ((N/H:ℕ):ℝ) ≤ (N:ℝ)/(H:ℝ) := by
      apply (le_div_iff₀ hHr).mpr
      exact_mod_cast Nat.div_mul_le_self N H
    have hdy : 1/(2:ℝ)^(N/H) = (2:ℝ)^(-((N/H:ℕ):ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    rw [hdy,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [div_eq_mul_inv,mul_neg,one_mul] using neg_le_neg hdiv
  · have hC := gaussianTripleBandConstant_pos
    rw [← ENNReal.ofReal_mul (by positivity),bad_triple_distance_factor hR]
    apply ENNReal.ofReal_le_ofReal
    have hD : 0 ≤ D := by
      dsimp [D]
      have hpow : (2:ℝ)^((h:ℝ)-ell) < 1 := by
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hC := gaussianTripleBandConstant_pos
      positivity
    have hd := radial_scale_window_decay hH hNh (j := N/H) le_rfl (sub_pos.mpr hell).le
    have he : ((2:ℝ)^(N/H))^((h:ℝ)-ell) = ((2:ℝ)^(N/H))^(-(ell-h)) := by congr 1; ring
    rw [he]
    calc
      _ = D*R^(2*(h:ℝ)*b+e)*(((2:ℝ)^(N/H))^(-(ell-h))) := by
        dsimp [D]
        rw [Real.rpow_add hR]
        ring
      _ ≤ D*R^(2*(h:ℝ)*b+e)*R^(-((ell-h)/(2*(H:ℝ)))) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hD (by positivity))
      _ = D*R^(-q) := by rw [mul_assoc,← Real.rpow_add hR]; congr 1; dsimp [q]; ring_nf
      _ ≤ R^(q/2)*R^(-q) := mul_le_mul_of_nonneg_right (hc N (by omega)) (by positivity)
      _ = R^(-(q/2)) := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI
