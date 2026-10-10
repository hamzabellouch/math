import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Difference
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadratic_difference_bound (B : E →L[ℝ] E →L[ℝ] ℝ) (q r : E) :
    |B q q-B r r| ≤ ‖B‖*‖q-r‖*(‖q‖+‖r‖) := by
  have he : B q q-B r r = B (q-r) q+B r (q-r) := by
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  have h1 : |B (q-r) q| ≤ ‖B‖*‖q-r‖*‖q‖ :=
    (B.le_opNorm₂ _ _)
  have h2 : |B r (q-r)| ≤ ‖B‖*‖r‖*‖q-r‖ :=
    (B.le_opNorm₂ _ _)
  nlinarith

theorem rounded_negative_curvature (B : E →L[ℝ] E →L[ℝ] ℝ) (q w : E)
    {a M s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s)
    (hBn : ‖B‖ ≤ M) (hwn : ‖w‖ ≤ 1) (hwl : 1-a/(4096*M) ≤ ‖w‖)
    (hcurv : B w w ≤ -(111/16:ℝ)*a*‖w‖^2)
    (hqn : ‖q‖ ≤ s) (hqw : ‖q-s • w‖ ≤ 9*s*(a/(1024*M))/8) :
    B q q ≤ -6*a*s^2 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hβ : a/(4096*M) ≤ (1/4096:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4096*M)).mpr
    calc
      a ≤ 1 := ha1
      _ ≤ (1/4096:ℝ)*(4096*M) := by nlinarith
  have hwl' : (4095/4096:ℝ) ≤ ‖w‖ := by linarith
  have hws : (4095/4096:ℝ)^2 ≤ ‖w‖^2 :=
    pow_le_pow_left₀ (by norm_num) hwl' 2
  have hrn : ‖s • w‖ ≤ s := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    nlinarith
  have hd := quadratic_difference_bound B q (s • w)
  have her : |B q q-B (s • w) (s • w)| ≤ (9/4096:ℝ)*a*s^2 := by
    apply hd.trans
    calc
      ‖B‖*‖q-s • w‖*(‖q‖+‖s • w‖) ≤
          M*(9*s*(a/(1024*M))/8)*(s+s) := by
        apply mul_le_mul
        · exact mul_le_mul hBn hqw (norm_nonneg _) (le_of_lt hMp)
        · exact add_le_add hqn hrn
        · positivity
        · positivity
      _ = (9/4096:ℝ)*a*s^2 := by field_simp; ring
  have hsB : B (s • w) (s • w)=s^2*B w w := by
    simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    ring
  rw [hsB] at her
  have hu := (abs_le.mp her).2
  have hc := mul_le_mul_of_nonneg_left hcurv (sq_nonneg s)
  have he := mul_le_mul_of_nonneg_left hws (show 0 ≤ (111/16:ℝ)*a*s^2 by positivity)
  nlinarith

end CurrentKS.Difference

end OAI
