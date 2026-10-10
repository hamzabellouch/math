import OAI.NumberTheory.TwoPoint.Halasz.HalaszHolderPowers
import OAI.NumberTheory.TwoPoint.Halasz.HalaszScaledMoment

namespace OAI

/-! The analytic estimate for a repeated coordinate in a Vinogradov
system. The scaled polynomial records the repeated variable exactly. -/
namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_torus_cauchy {d : ℕ}
    (F G : (Fin d → AddCircle (1:ℝ)) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0≤F x) (hG0 : ∀ x, 0≤G x) :
    (∫ x, F x*G x ∂halaszVinogradovHaar d)^2 ≤
      (∫ x, (F x)^2 ∂halaszVinogradovHaar d) *
        (∫ x, (G x)^2 ∂halaszVinogradovHaar d) := by
  have h := halasz_holder_integer_power (by omega : 2≤2)
    (fun x => (F x)^2) (fun x => (G x)^2)
    (hF.pow 2) (hG.pow 2) (fun x => sq_nonneg _) (fun x => sq_nonneg _)
  have hs (x : ℝ) (hx : 0≤x) : (x^2)^(1/(2:ℝ))=x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx]
    norm_num
  norm_num only [Nat.cast_ofNat,show (1:ℝ)-1/2=1/2 by norm_num,
    hs _ (hF0 _),hs _ (hG0 _),Nat.reduceSub,pow_one] at h
  exact h

lemma halasz_collision_interpoland {s k : ℕ} (hk : 2≤k)
    {f g : ℝ} (hf : 0≤f) (hg : 0≤g) :
    (f^(2*(s+k)))^(1-1/(k:ℝ)) *
        (f^(2*s)*g^k)^(1/(k:ℝ)) = f^(2*(s+k)-2)*g := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  have he : ((2*(s+k):ℕ):ℝ)*(1-1/(k:ℝ)) + ((2*s:ℕ):ℝ)*(1/(k:ℝ)) =
      ((2*(s+k)-2:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 2≤2*(s+k))]
    push_cast
    field_simp
    ring
  rw [Real.mul_rpow (pow_nonneg hf _) (pow_nonneg hg _)]
  simp only [← Real.rpow_natCast,← Real.rpow_mul hf,← Real.rpow_mul hg]
  rw [← mul_assoc,← Real.rpow_add' hf]
  · rw [he,mul_one_div_cancel hk0,Real.rpow_one,Real.rpow_natCast]
  · rw [he]
    exact_mod_cast (by omega : 2*(s+k)-2≠0)

noncomputable def halaszCollisionMoment (s k N : ℕ) : ℝ :=
  ∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*(s+k)-2) *
    ‖halaszScaledPolynomial k N 2 α‖ ∂halaszVinogradovHaar k

theorem halasz_collision_moment_bound {s k : ℕ} (hs : 0<s) (hk : 2≤k) (N : ℕ) :
    (halaszCollisionMoment s k N)^(2*k) ≤
      (halaszVinogradovCount (s+k) k N:ℝ)^(2*k-1) *
        (halaszVinogradovCount s k N:ℝ) := by
  let F := fun α => ‖halaszVinogradovPolynomial k N α‖
  let G := fun α => ‖halaszScaledPolynomial k N 2 α‖
  have hF : Continuous F := (halasz_finite_phase_continuous _ _).norm
  have hG : Continuous G := (halasz_scaled_polynomial_continuous k N 2).norm
  have hF0 : ∀ α, 0≤F α := fun _ => norm_nonneg _
  have hG0 : ∀ α, 0≤G α := fun _ => norm_nonneg _
  let B := fun α => (F α)^(2*s)*(G α)^k
  have hB : Continuous B := (hF.pow _).mul (hG.pow _)
  have hB0 : ∀ α, 0≤B α := fun α => mul_nonneg (pow_nonneg (hF0 α) _)
    (pow_nonneg (hG0 α) _)
  have hI := halasz_holder_integer_power hk (fun α => (F α)^(2*(s+k))) B
    (hF.pow _) hB (fun α => pow_nonneg (hF0 α) _) hB0
  have heq (α : Fin k → AddCircle (1:ℝ)) :
      ((F α)^(2*(s+k)))^(1-1/(k:ℝ))*(B α)^(1/(k:ℝ)) =
        (F α)^(2*(s+k)-2)*G α :=
    halasz_collision_interpoland hk (hF0 α) (hG0 α)
  simp_rw [heq] at hI
  change (halaszCollisionMoment s k N)^k ≤ _ at hI
  rw [halasz_vinogradov_real_moment] at hI
  have hC := halasz_torus_cauchy (fun α => (F α)^s*(G α)^k)
    (fun α => (F α)^s) ((hF.pow _).mul (hG.pow _)) (hF.pow _)
    (fun α => mul_nonneg (pow_nonneg (hF0 α) _) (pow_nonneg (hG0 α) _))
    (fun α => pow_nonneg (hF0 α) _)
  have hprod (α : Fin k → AddCircle (1:ℝ)) :
      ((F α)^s*(G α)^k)*(F α)^s=B α := by dsimp [B]; ring
  simp_rw [hprod,mul_pow,← pow_mul,Nat.mul_comm s 2,Nat.mul_comm k 2] at hC
  rw [halasz_vinogradov_real_moment] at hC
  have hM := halasz_scaled_mixed_moment hs (by omega : 0<k) k N 2 (by norm_num)
  have hC' : (∫ α, B α ∂halaszVinogradovHaar k)^2 ≤
      (halaszVinogradovCount (s+k) k N:ℝ)*(halaszVinogradovCount s k N:ℝ) :=
    hC.trans (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _))
  have hpow := pow_le_pow_left₀ (pow_nonneg
    (integral_nonneg (fun α => mul_nonneg (pow_nonneg (hF0 α) _) (hG0 α))) _) hI 2
  rw [mul_pow] at hpow
  have h := hpow.trans (mul_le_mul_of_nonneg_left hC'
    (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
  rw [← pow_mul,← pow_mul,← mul_assoc,← pow_succ,
    show k*2=2*k by omega,show (k-1)*2+1=2*k-1 by omega] at h
  exact h

end TwoPointCorrelations

end OAI
