import OAI.NumberTheory.TotientAsymptotic.IntervalEulerBound
import OAI.NumberTheory.TotientAsymptotic.IntervalPrimeMass

namespace OAI

/-! The interval prime-factor moment with its correct log-log exponent. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

 theorem interval_omega_moment_bound : ∃ C : ℝ, 0<C ∧
    ∀ a : ℝ, 0≤a → a≤3/2 → ∀ N : ℕ, 2≤N →
    ∀ U T : ℝ, 2≤U → U≤T → T≤N → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n≤N) →
    (∑ n ∈ Q,intervalOmegaWeight a U T n) ≤
      C*Real.log N*Real.exp ((a-1)*(B T-B U)) := by
  obtain ⟨D,hD,herr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp (3*D+9),Real.exp_pos _,?_⟩
  intro a ha ha' N hN U T hU hUT hTN Q hQ
  have hNR : (2:ℝ)≤N := by exact_mod_cast hN
  have hT : 2≤T := hU.trans hUT
  have hNerr := herr N hNR
  have hTerr := herr T hT
  have hUerr := herr U hU
  have hinterval : |(primeReciprocalLE T-primeReciprocalLE U)-(B T-B U)|≤2*D := by
    have h := abs_sub_le (primeReciprocalLE T-B T) 0 (primeReciprocalLE U-B U)
    simp only [sub_zero,zero_sub,abs_neg] at h
    have he : (primeReciprocalLE T-B T)-(primeReciprocalLE U-B U) =
        (primeReciprocalLE T-primeReciprocalLE U)-(B T-B U) := by ring
    rw [he] at h
    linarith
  have haabs : |a-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hmul : (a-1)*((primeReciprocalLE T-primeReciprocalLE U)-(B T-B U))≤2*D := by
    calc
      _ ≤ |(a-1)*((primeReciprocalLE T-primeReciprocalLE U)-(B T-B U))| := le_abs_self _
      _ = |a-1| * |(primeReciprocalLE T-primeReciprocalLE U)-(B T-B U)| := abs_mul _ _
      _ ≤ 1*(2*D) := mul_le_mul haabs hinterval (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hmass : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)=primeReciprocalLE N := by
    simp only [primeReciprocalLE,primesUpTo,Nat.floor_natCast]
  have hexp : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)+
      (a-1)*(∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9 ≤
      (3*D+9)+B N+(a-1)*(B T-B U) := by
    rw [hmass,prime_interval_sum_eq N hU hUT hTN]
    have hh := (abs_le.mp hNerr).2
    nlinarith
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  calc
    _ ≤ ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        (1-(if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ))⁻¹ :=
      interval_omega_moment_product ha ha' U T N Q hQ
    _ ≤ Real.exp ((∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)+
        (a-1)*(∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
          (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9) :=
      interval_euler_product_bound ha ha' U T N
    _ ≤ Real.exp ((3*D+9)+B N+(a-1)*(B T-B U)) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add,Real.exp_add]; simp only [B,Real.exp_log hlog]

end TotientAsymptotic

end

end OAI
