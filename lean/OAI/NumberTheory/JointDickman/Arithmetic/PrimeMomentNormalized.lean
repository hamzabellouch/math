import OAI.NumberTheory.JointDickman.Arithmetic.PrimeReciprocalSquareMass
import OAI.NumberTheory.TwoPointCorrelations.MRTLargeValues
import OAI.NumberTheory.TwoPointCorrelations.Basic

namespace OAI

/-! # A fixed prime moment at its natural reciprocal normalization -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

theorem fixed_prime_moment_large_bound (r : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ a : ℝ, Real.exp 1 ≤ a → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ f : ℕ → ℂ, OneBounded f → ∀ U : Finset ℝ,
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, |t| ≤ a^r) → ∀ V : ℝ, 0 < V →
      (∀ t ∈ U, V ≤ ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t‖) →
      (U.card:ℝ) ≤ C*(Real.log a)^2/V^(2*r) := by
  obtain ⟨D,hD,hmass⟩ := prime_reciprocal_square_mass
  let C := 8*Real.exp 1*(2+(3:ℝ)^r)*(2+9*(r:ℝ)^2)*(r.factorial:ℝ)*D^r
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro a ha Q hQ f hf U hsep hU V hV hlarge
  have ha1 : 1 ≤ a := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans ha
  have ha0 : 0 < a := by linarith
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlog : 1 ≤ Real.log a := by simpa using Real.log_le_log (Real.exp_pos 1) ha
  let M := ⌈2*a⌉₊
  have hMlo : 2*a ≤ (M:ℝ) := Nat.le_ceil _
  have hMhi : (M:ℝ) ≤ 3*a := by
    have hh := Nat.ceil_lt_add_one (show 0≤2*a by positivity)
    dsimp [M]
    linarith
  have hM0 : 0 < (M:ℝ) := by linarith
  have hcoeff : (∑ p ∈ Q, ‖f p/(p:ℂ)‖^2) ≤ D/a := by
    calc
      _ ≤ ∑ p ∈ Q, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        rw [norm_div,Complex.norm_natCast,div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith [hf p (hQ p hp).1.pos,norm_nonneg (f p)]
      _ ≤ D/(a*Real.log a) := hmass a ha2 Q hQ
      _ ≤ D/a := div_le_div_of_nonneg_left hD.le ha0 (by nlinarith)
  have hbound := mrt_prime_large_values Q (fun p => f p/(p:ℂ)) M r
    (fun p hp => (hQ p hp).1)
    (fun p hp => by exact_mod_cast (hQ p hp).2.2.trans hMlo) U
    (show 0 ≤ a^r by positivity) hV hU hsep hlarge
  have hpow : ((M^r:ℕ):ℝ) ≤ (3:ℝ)^r*a^r := by
    simpa only [Nat.cast_pow,mul_pow] using pow_le_pow_left₀ hM0.le hMhi r
  have hfirst : a^r+1+((M^r:ℕ):ℝ) ≤ (2+(3:ℝ)^r)*a^r := by
    have hh : 1 ≤ a^r := one_le_pow₀ ha1
    nlinarith
  have hlogM : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by linarith)
  have hlogMu : Real.log (M:ℝ) ≤ 3*Real.log a := by
    have hh := Real.log_le_log hM0 hMhi
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) ha0.ne'] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have hsecond : 2+(Real.log ((M^r:ℕ):ℝ))^2 ≤ (2+9*(r:ℝ)^2)*(Real.log a)^2 := by
    rw [Nat.cast_pow,Real.log_pow]
    have hp := pow_le_pow_left₀ hlogM hlogMu 2
    have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (r:ℝ))
    nlinarith [sq_nonneg (Real.log a-1),sq_nonneg (r:ℝ)]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hV.le _)
  calc
    _ ≤ (8*Real.exp 1*((2+(3:ℝ)^r)*a^r)*
        ((2+9*(r:ℝ)^2)*(Real.log a)^2)*(r.factorial:ℝ))*(D/a)^r := by
      gcongr
    _ = C*(Real.log a)^2 := by
      dsimp [C]
      rw [div_pow]
      field_simp

end JointDickman

end OAI
