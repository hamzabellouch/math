import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelEnergy
import OAI.NumberTheory.CubicMoment.Estimates.PolynomialMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.HeightSquareRoot

namespace OAI

/-! The undecomposed prime model at large heights. The norm fibre has
size at most two, so Montgomery--Vaughan gives its genuine mean square
without a divisor loss or an assumed model cancellation estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma prime_model_coefficient_energy (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ X ≤ norm p ∧ norm p ≤ 2*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) :
    (∑ p ∈ P, ‖c p*((norm p^(-1/6:ℝ):ℝ):ℂ)‖^2) ≤
      36*M^2*X^(2/3:ℝ) := by
  have hcard : (P.card:ℝ) ≤ 36*X := by
    have hs : P ⊆ nonzeroNormBall (2*X) := by
      intro p hp
      exact mem_nonzeroNormBall.mpr ⟨(hP p hp).2.2,(hP p hp).1.2.ne_zero⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
      (by simpa only [show (18:ℝ)*(2*X) = 36*X by ring] using
        nonzeroNormBall_card_le (show 0 ≤ 2*X by positivity))
  have hp (p : Eisenstein) (hp : p ∈ P) :
      ‖c p*((norm p^(-1/6:ℝ):ℝ):ℂ)‖^2 ≤ M^2*X^(-1/3:ℝ) := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg p) _)]
    have hn : (norm p^(-1/6:ℝ))^2 ≤ X^(-1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg p)]
      norm_num
      exact Real.rpow_le_rpow_of_nonpos hX (hP p hp).2.1 (by norm_num)
    exact mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _) (hc p hp) 2) hn
      (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ (P.card:ℝ)*(M^2*X^(-1/3:ℝ)) := by simpa using Finset.sum_le_sum hp
    _ ≤ (36*X)*(M^2*X^(-1/3:ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 36*M^2*X^(2/3:ℝ) := by
      have he : X*X^(-1/3:ℝ) = X^(2/3:ℝ) := by
        nth_rw 1 [← Real.rpow_one X]
        rw [← Real.rpow_add hX]
        norm_num
      calc
        _ = 36*M^2*(X*X^(-1/3:ℝ)) := by ring
        _ = _ := by rw [he]

theorem prime_model_height_mean_square {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T M : ℝ} (hX : 0 < X) (hT : 0 < T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t =>
      ‖dispersionModel P (fun p => c p*theta ℓ p) (t+u)‖^2) T ≤
      144*C*M^2*(1+4*X/T)*X^(2/3:ℝ) := by
  let N := ⌊4*X⌋₊
  let v := fun p => c p*((norm p^(-1/6:ℝ):ℝ):ℂ)
  have hN : (N:ℝ) ≤ 4*X := Nat.floor_le (by positivity)
  have hi : ∀ p ∈ P, normNat p ∈ Finset.Icc 1 N := by
    intro p hp
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (hP p hp).1.2.ne_zero),?_⟩
    apply Nat.le_floor
    simpa only [normNat_cast] using (hP p hp).2
  have hf : ∀ n ∈ Finset.Icc 1 N,
      ((P.filter (fun p => normNat p = n)).card:ℝ) ≤ 2 := by
    intro n hn
    have hh := prime_norm_fiber_card_le_two P (fun p hp => (hP p hp).1) (n:ℤ)
    have hn' : (P.filter (fun p => (normNat p:ℤ) = (n:ℤ))) =
        P.filter (fun p => normNat p = n) := by ext; simp
    rw [hn'] at hh
    exact_mod_cast hh
  have hb := fixedAngular_translated_dyadicMeanSquare hMV hC P v N 2 hi
    (fun p hp => (hP p hp).1.2.ne_zero) hf ℓ u hT
  have he (t : ℝ) :
      (∑ p ∈ P, v p*theta ℓ p*mellinPhase (t+u) (norm p)) =
        dispersionModel P (fun p => c p*theta ℓ p) (t+u) := by
    unfold dispersionModel v
    apply Finset.sum_congr rfl
    intro p hp
    rw [normTwist_eq_mellinPhase]
    ring
  simp_rw [he] at hb
  change dyadicHeightMean _ T ≤ _
  change dyadicHeightMean _ T ≤ _ at hb
  have henergy := prime_model_initial_segment_energy P c hX hM hP hc
  have hfactor : 1+(N:ℝ)/T ≤ 1+4*X/T :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hN hT.le)
  apply hb.trans
  calc
    _ ≤ 2*C*(1+4*X/T)*2*(36*M^2*X^(2/3:ℝ)) := by
      apply mul_le_mul
      · gcongr
      · exact henergy
      · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · positivity
    _ = _ := by ring

lemma continuous_prime_model_height (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t => dispersionModel P (fun p => c p*theta ℓ p) (t+u)) := by
  unfold dispersionModel
  apply continuous_finsetSum
  intro p hp
  exact (continuous_const.mul ((continuous_normTwist p).comp
    (continuous_id.add continuous_const))).mul continuous_const

theorem prime_model_height_mean_absolute {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T M : ℝ} (hX : 0 < X) (hT : 0 < T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t =>
      ‖dispersionModel P (fun p => c p*theta ℓ p) (t+u)‖) T ≤
      2*Real.sqrt (144*C*M^2*(1+4*X/T)*X^(2/3:ℝ)) := by
  exact dyadicHeightMean_norm_le_sqrt (continuous_prime_model_height P c ℓ u) hT
    (by positivity) (prime_model_height_mean_square hMV hC P c hX hT hM hP hc ℓ u)

/-- Large-height decay for the actual prime model. Only ordinary polynomial
mean value and the prime norm multiplicity are used. -/
theorem prime_model_height_power_saving {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T M δ : ℝ} (hX : 1 ≤ X) (hTX : T ≤ X) (hTδ : X^δ ≤ T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t =>
      ‖dispersionModel P (fun p => c p*theta ℓ p) (t+u)‖) T ≤
      2*Real.sqrt (720*C)*M*X^(5/6-δ/2) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hT : 0 < T := (Real.rpow_pos_of_pos hXp δ).trans_le hTδ
  have hf : 1+4*X/T ≤ 5*(X/X^δ) := by
    have hratio : 1 ≤ X/T := (le_div_iff₀ hT).mpr (by simpa using hTX)
    have ht : X/T ≤ X/X^δ := div_le_div_of_nonneg_left hXp.le
      (Real.rpow_pos_of_pos hXp δ) hTδ
    calc
      1+4*X/T = 1+4*(X/T) := by ring
      _ ≤ 5*(X/T) := by linarith
      _ ≤ 5*(X/X^δ) := by linarith
  have he : (144*C*M^2*(1+4*X/T)*X^(2/3:ℝ)) ≤
      (Real.sqrt (720*C)*M*X^(5/6-δ/2))^2 := by
    calc
      _ ≤ 144*C*M^2*(5*(X/X^δ))*X^(2/3:ℝ) := by gcongr
      _ = (720*C)*M^2*X^(5/3-δ) := by
        have hx : (X/X^δ)*X^(2/3:ℝ) = X^(5/3-δ) := by
          nth_rw 1 [← Real.rpow_one X]
          rw [← Real.rpow_sub hXp, ← Real.rpow_add hXp]
          congr 1
          ring
        calc
          _ = (720*C)*M^2*((X/X^δ)*X^(2/3:ℝ)) := by ring
          _ = _ := by rw [hx]
      _ = _ := by
        have hx : (X^(5/6-δ/2))^2 = X^(5/3-δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
          congr 1
          ring
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hx]
  have hb := dyadicHeightMean_norm_le_of_sq_le_nonneg
    (continuous_prime_model_height P c ℓ u) hT (by positivity)
    ((prime_model_height_mean_square hMV hC P c hXp hT hM hP hc ℓ u).trans he)
  simpa only [mul_assoc] using hb

end CubicFirstMoment

end

end OAI
