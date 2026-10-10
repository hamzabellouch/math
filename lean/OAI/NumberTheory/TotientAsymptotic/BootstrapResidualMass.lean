import OAI.NumberTheory.TotientAsymptotic.TwoPrimeResidualMass
import OAI.NumberTheory.TotientAsymptotic.PreimageLoglogBound

namespace OAI

/-! The exact residual-value set has mass controlled at the smaller endpoint. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma bootstrap_prime_endpoint {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    2 ≤ ⌊2*x^2⌋₊ ∧ 0 ≤ B (⌊2*x^2⌋₊:ℝ) ∧ B (⌊2*x^2⌋₊:ℝ) ≤ 3*B x := by
  have he : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx3 : 3 ≤ x := by
    have ht := Real.add_one_le_exp (Real.exp (1:ℝ))
    linarith
  have hfloor : 4 ≤ ⌊2*x^2⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hN4 : (4:ℝ) ≤ ⌊2*x^2⌋₊ := by exact_mod_cast hfloor
  have hN : (⌊2*x^2⌋₊:ℝ) ≤ 2*x^2 := Nat.floor_le (by positivity)
  have hlogN : 1 ≤ Real.log (⌊2*x^2⌋₊:ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0:ℝ)<4) hN4
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at ht
    norm_num only [Nat.cast_ofNat] at ht
    linarith [Real.log_two_gt_d9]
  refine ⟨by omega,Real.log_nonneg hlogN,?_⟩
  have hmono : B (⌊2*x^2⌋₊:ℝ) ≤ B (2*x^2) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by linarith) hN)
  exact hmono.trans (doubleLog_twice_square hx)

 theorem bootstrap_residual_mass : ∃ C : ℝ,0 < C ∧ ∀ x : ℝ,
    Real.exp (Real.exp 1) ≤ x → ∀ J : ℕ,1 ≤ J → ∀ M : Finset ℕ,
    (∀ m ∈ M,IsTotient m ∧ (m:ℝ) ≤ (2:ℝ)^J) →
    (∑ d ∈ singlePrimeExtensions (Nat.primesLE ⌊2*x^2⌋₊) M,(d:ℝ)⁻¹) ≤
      C*(1+B x)*dyadicTotientEnvelope J*(1+Real.log J) := by
  obtain ⟨D,hD,hmass⟩ := prime_reciprocal_mass_bound mertensProductInput
  refine ⟨5*(1+6*D),by positivity,?_⟩
  intro x hx J hJ M hM
  obtain ⟨hN,hBN,hBNx⟩ := bootstrap_prime_endpoint hx
  have hp := hmass _ hN hBN
  have hBx : 0 ≤ B x := by linarith
  have hlog : 0 ≤ Real.log (J:ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hE := dyadicTotientEnvelope_one_le J
  have hprime : 1+2*(∑ p ∈ Nat.primesLE ⌊2*x^2⌋₊,((p-1:ℕ):ℝ)⁻¹) ≤
      (1+6*D)*(1+B x) := by nlinarith
  have hM' := dyadic_totient_reciprocal_mass hJ M hM
  have hM'' : (∑ m ∈ M,(m:ℝ)⁻¹) ≤ 5*dyadicTotientEnvelope J*(1+Real.log J) := by nlinarith
  calc
    _ ≤ (1+2*∑ p ∈ Nat.primesLE ⌊2*x^2⌋₊,((p-1:ℕ):ℝ)⁻¹)*(∑ m ∈ M,(m:ℝ)⁻¹) :=
      singlePrimeExtensions_mass _ _ (fun p hp => (Nat.mem_primesLE.mp hp).2)
    _ ≤ ((1+6*D)*(1+B x))*(5*dyadicTotientEnvelope J*(1+Real.log J)) :=
      mul_le_mul hprime hM'' (Finset.sum_nonneg (fun m _ => inv_nonneg.mpr (Nat.cast_nonneg _))) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
