import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleWindow

namespace OAI

/-! Removing the localization volume from the double mean-value estimate. -/
namespace TwoPointCorrelations

open Finset

noncomputable def halaszDoubleWeight {k : ℕ} (r s M₁ M₂ : ℕ)
    (γ : Fin k → ℝ) (j : Fin k) : ℝ :=
  min (2*((s*M₂^(j.val+1):ℕ):ℝ)+1)
    (8*((s*M₂^(j.val+1):ℕ):ℝ)*halaszDoubleWindow r M₁ j+
      2*((s*M₂^(j.val+1):ℕ):ℝ)* |γ j| +8*halaszDoubleWindow r M₁ j/ |γ j| +2)

theorem halasz_double_specialized (k M₁ M₂ r s : ℕ) (hr : 1≤r) (hs : 1≤s)
    (hM₁ : 1≤M₁) (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) :
    ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      (32*(r:ℝ))^k*(M₁:ℝ)^(∑ j : Fin k, (j.val+1))*
        (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
          (halaszVinogradovCount r k M₁:ℝ)*(halaszVinogradovCount s k M₂:ℝ)*
            ∏ j,halaszDoubleWeight r s M₁ M₂ γ j := by
  let δ : Fin k → ℝ := halaszDoubleWindow r M₁
  let P := ∏ j,δ j
  let Q := (16*(r:ℝ))^k*(M₁:ℝ)^(∑ j : Fin k, (j.val+1))
  let C := (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
    (halaszVinogradovCount r k M₁:ℝ)
  let U := (halaszVinogradovCount s k M₂:ℝ)*∏ j,halaszDoubleWeight r s M₁ M₂ γ j
  have hP : 0<P := prod_pos (fun j _ => halasz_double_window_pos hr hM₁ j)
  have hPQ : P*Q=1 := halasz_double_window_product hr hM₁
  have hQ : 0≤Q := by
    dsimp only [Q]
    positivity
  have htwo : (∏ j : Fin k,2*δ j)=(2:ℝ)^k*P := by
    rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
  have hd := halasz_double_mean_value k M₁ M₂ r s hr hs γ δ hγ
    (fun j => (halasz_double_window_pos hr hM₁ j).le)
    (fun j => halasz_double_window_small hr hM₁ j)
    (fun j => halasz_double_window_phase hr hM₁ j)
  have hscaled : P^2*
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      C*((2:ℝ)^k*P)*U := by
    convert hd using 1
    dsimp only [C,U,halaszDoubleWeight]
    rw [htwo]
    ring
  have hcancel : P*
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      C*(2:ℝ)^k*U := by
    apply (mul_le_mul_iff_right₀ hP).mp
    convert hscaled using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hcancel hQ
  have hpw : (16*(r:ℝ))^k*(2:ℝ)^k=(32*(r:ℝ))^k := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = Q*(P*‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s)) := by
      rw [← mul_assoc,mul_comm Q P,hPQ,one_mul]
    _ ≤ Q*(C*(2:ℝ)^k*U) := hmul
    _ = ((16*(r:ℝ))^k*(2:ℝ)^k)*(M₁:ℝ)^(∑ j : Fin k, (j.val+1))*C*U := by
      dsimp only [Q]
      ring
    _ = _ := by rw [hpw]; dsimp only [C,U]; ring

end TwoPointCorrelations

end OAI
