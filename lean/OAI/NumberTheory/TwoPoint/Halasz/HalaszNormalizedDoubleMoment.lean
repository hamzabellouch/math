import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightNormalization
import OAI.NumberTheory.TwoPoint.Halasz.HalaszQuantitativeMeanValue

namespace OAI

/-! Cancellation of the two complete-system degree costs against the
coordinate volumes in the double moment. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_coordinate_degree (k : ℕ) :
    (∑ j : Fin k, ((j.val+1:ℕ):ℝ))=(k:ℝ)*(k+1)/2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    push_cast
    ring

lemma halasz_coordinate_total_degree {k : ℕ} (hk : 0<k) :
    ((∑ j : Fin k, (j.val+1):ℕ):ℝ)=(halaszTotalDegree k:ℝ) := by
  rw [halasz_total_degree_cast hk]
  simpa only [Nat.cast_sum] using halasz_coordinate_degree k

lemma halasz_normalized_weight_nonneg {k r M : ℕ} (γ : Fin k → ℝ) (j : Fin k) :
    0≤halaszNormalizedWeight r M γ j := by
  unfold halaszNormalizedWeight
  positivity

lemma halasz_double_weight_nonneg {k r s M₁ M₂ : ℕ} (γ : Fin k → ℝ) (j : Fin k) :
    0≤halaszDoubleWeight r s M₁ M₂ γ j := by
  unfold halaszDoubleWeight halaszDoubleWindow
  positivity

theorem halasz_normalized_double_moment {k r M : ℕ} (hr : 1≤r) (hM : 1≤M)
    (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) {C ε : ℝ}
    (hJ : (halaszVinogradovCount r k M:ℝ)≤
      C*(M:ℝ)^(2*(r:ℝ)-((∑ j : Fin k,(j.val+1):ℕ):ℝ)+ε)) :
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*r) ≤
      (32*(r:ℝ))^k*C^2*(M:ℝ)^(4*(r:ℝ)^2+2*ε)*
        ∏ j,halaszNormalizedWeight r M γ j := by
  let K := ∑ j : Fin k,(j.val+1)
  let e : ℝ := 2*(r:ℝ)-(K:ℝ)+ε
  let W := ∏ j,halaszNormalizedWeight r M γ j
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hW0 : 0≤W := prod_nonneg (fun j _ => halasz_normalized_weight_nonneg γ j)
  have hweights : (∏ j,halaszDoubleWeight r r M M γ j)≤(M:ℝ)^K*W := by
    calc
      _ ≤ ∏ j : Fin k,(M:ℝ)^(j.val+1)*halaszNormalizedWeight r M γ j :=
        prod_le_prod₀ (fun j _ => halasz_double_weight_nonneg γ j)
          (fun j _ => halasz_weight_normalized hr hM γ hγ j)
      _ = _ := by rw [prod_mul_distrib,prod_pow_eq_pow_sum]
  have hJ2 : (halaszVinogradovCount r k M:ℝ)^2≤(C*(M:ℝ)^e)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2
  have hbase := halasz_double_specialized k M M r r hr hr hM γ hγ
  have hbound :
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*r) ≤
      (32*(r:ℝ))^k*(M:ℝ)^K*(M:ℝ)^((r-1)*(2*r))*(M:ℝ)^(r*(2*r-2))*
        (C*(M:ℝ)^e)^2*((M:ℝ)^K*W) := by
    apply hbase.trans
    calc
      _ = (32*(r:ℝ))^k*(M:ℝ)^K*(M:ℝ)^((r-1)*(2*r))*(M:ℝ)^(r*(2*r-2))*
          (halaszVinogradovCount r k M:ℝ)^2*(∏ j,halaszDoubleWeight r r M M γ j) := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left hJ2 (by positivity)) hweights
        (prod_nonneg (fun j _ => halasz_double_weight_nonneg γ j)) (by positivity)
  apply hbound.trans_eq
  have hr2 : 2≤2*r := by omega
  have hexp : (K:ℝ)+(((r-1)*(2*r):ℕ):ℝ)+((r*(2*r-2):ℕ):ℝ)+2*e+(K:ℝ)=
      4*(r:ℝ)^2+2*ε := by
    dsimp only [e]
    push_cast [Nat.cast_sub hr,Nat.cast_sub hr2]
    ring
  calc
    _ = (32*(r:ℝ))^k*C^2*
        ((M:ℝ)^K*(M:ℝ)^((r-1)*(2*r))*(M:ℝ)^(r*(2*r-2))*
          ((M:ℝ)^e)^2*(M:ℝ)^K)*W := by ring
    _ = (32*(r:ℝ))^k*C^2*(M:ℝ)^(4*(r:ℝ)^2+2*ε)*W := by
      rw [← Real.rpow_natCast (M:ℝ) K,← Real.rpow_natCast (M:ℝ) ((r-1)*(2*r)),
        ← Real.rpow_natCast (M:ℝ) (r*(2*r-2)),
        ← Real.rpow_natCast ((M:ℝ)^e) 2,← Real.rpow_mul hM0.le]
      rw [← Real.rpow_add hM0,← Real.rpow_add hM0,← Real.rpow_add hM0,
        ← Real.rpow_add hM0]
      norm_num only [Nat.cast_ofNat]
      rw [show (K:ℝ)+(((r-1)*(2*r):ℕ):ℝ)+((r*(2*r-2):ℕ):ℝ)+e*2+(K:ℝ)=
        4*(r:ℝ)^2+2*ε by nlinarith only [hexp]]

end TwoPointCorrelations

end OAI
