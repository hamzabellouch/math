import OAI.Dynamics.StandardMap.StablePrefix

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma real_axes_decomposition (s : ℂ) : s=s.re • (1:ℂ)+s.im • Complex.I := by
  apply Complex.ext <;> simp
lemma row_axes_decomposition (row : ℂ →L[ℝ] ℝ) (s : ℂ) :
    row s=s.re*row 1+s.im*row Complex.I := by
  conv_lhs => rw [real_axes_decomposition s]
  simp only [map_add,map_smul,smul_eq_mul]

lemma normalized_kernel_from_stable (row : ℂ →L[ℝ] ℝ) (s : ℂ) (D : ℝ)
    (hD : 0 < D) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4)
    (hrow : D/3 ≤ |row 1|) (hsmall : |row s| ≤ D⁻¹) :
    ∃ (u : ℂ) (e : ℝ), u.im=1 ∧ row u=0 ∧
      u=(s.im)⁻¹ • s+e • (1:ℂ) ∧ |e| ≤ 6/D^2 := by
  have him := vertical_im_lower s hu hs
  have hsim : s.im ≠ 0 := abs_pos.mp (by linarith : 0 < |s.im|)
  have hr1 : row 1 ≠ 0 := abs_pos.mp (by linarith : 0 < |row 1|)
  let u : ℂ := (-row Complex.I/row 1) • (1:ℂ)+Complex.I
  let e := -row s/(row 1*s.im)
  refine ⟨u,e,?_,?_,?_,?_⟩
  · simp [u]
  · simp only [u,map_add,map_smul,smul_eq_mul]
    field_simp
    ring
  · have haxes:=row_axes_decomposition row s
    apply Complex.ext
    · simp only [u,Complex.add_re,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one,Complex.I_re,add_zero]
      dsimp [e]
      field_simp
      nlinarith
    · simp only [u,Complex.add_im,Complex.smul_im,Complex.one_im,smul_eq_mul,mul_zero,Complex.I_im,zero_add,add_zero]
      exact (inv_mul_cancel₀ hsim).symm
  · have hden : 0 < |row 1| *|s.im| := mul_pos (abs_pos.mpr hr1) (abs_pos.mpr hsim)
    dsimp [e]
    rw [abs_div,abs_neg,abs_mul]
    apply (div_le_iff₀ hden).mpr
    have hprod : D/6 ≤ |row 1| *|s.im| := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 6/D^2)
    have he : (6/D^2)*(D/6)=D⁻¹ := by field_simp
    rw [he] at hh
    exact hsmall.trans hh
lemma eligible_row_contraction (A : ℕ → ℂ →L[ℝ] ℂ) (s u : ℂ) (e M D : ℝ)
    (B l : ℕ) (_hl : 1 ≤ l) (hlB : l ≤ B) (hM : 1 < M)
    (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4)
    (heq : u=(s.im)⁻¹ • s+e • (1:ℂ)) (he : |e| ≤ 6/D^2)
    (hD : M^((49/50:ℝ)*(B:ℝ)) ≤ D)
    (hstable : ‖A l s‖ ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)))
    (hup : ‖A l‖ ≤ M^(l:ℝ)) :
    ‖A l u‖ ≤ 12*M^(-(47/50:ℝ)*(l:ℝ)) := by
  have hp : 0 < M := by linarith
  have hDpos : 0 < D := (Real.rpow_pos_of_pos hp _).trans_le hD
  have him:=vertical_im_lower s hu hs
  have hi : |(s.im)⁻¹| ≤ 2 := by
    rw [abs_inv]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < |s.im|)).mpr
    linarith
  have he' : |e| ≤ 6*M^(-(49/25:ℝ)*(B:ℝ)) := by
    calc
      _ ≤ 6/D^2 := he
      _ ≤ 6/(M^((49/50:ℝ)*(B:ℝ)))^2 := by gcongr
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hp.le,div_eq_mul_inv,← Real.rpow_neg hp.le]
        congr 2
        ring
  have herror : |e| * M^(l:ℝ) ≤ 6*M^(-(47/50:ℝ)*(l:ℝ)) := by
    calc
      _ ≤ 6*M^(-(49/25:ℝ)*(B:ℝ))*M^(l:ℝ) := mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg hp.le _)
      _ = 6*M^(-(49/25:ℝ)*(B:ℝ)+(l:ℝ)) := by rw [Real.rpow_add hp]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le ?_) (by norm_num)
        have hlR : (l:ℝ) ≤ B := by exact_mod_cast hlB
        have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
        linarith
  rw [heq,map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(s.im)⁻¹ • A l s‖+‖e • A l 1‖ := norm_add_le _ _
    _ = |(s.im)⁻¹| *‖A l s‖+|e| *‖A l 1‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ 2*(3*M^(-(47/50:ℝ)*(l:ℝ)))+|e| *M^(l:ℝ) := by
      apply add_le_add (mul_le_mul hi hstable (norm_nonneg _) (by norm_num))
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact ((A l).le_opNorm 1).trans (by simpa using hup)
    _ ≤ _ := by linarith
end StandardMapEntropy

end OAI
