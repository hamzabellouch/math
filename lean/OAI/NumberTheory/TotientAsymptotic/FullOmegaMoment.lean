import OAI.NumberTheory.TotientAsymptotic.IntervalMomentBound

namespace OAI

/-! The sharp three-halves moment needed for the small-prime-factor excess. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma omegaIn_all_factors {n N : ℕ} (hn : 0<n) (hnN : n≤N) :
    omegaIn n 1 N = n.primeFactorsList.length := by
  unfold omegaIn
  rw [List.filter_eq_self.mpr]
  intro p hp
  simp only [decide_eq_true_eq]
  constructor
  · exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).one_lt
  · exact_mod_cast (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hp)).trans hnN

/-- The exponent three used in coarse extraction bounds is sharpened to three
halves here, as required by the normality exception estimate. -/
theorem full_omega_moment_bound : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2≤N →
    ∀ Q : Finset ℕ, (∀ n ∈ Q,0<n ∧ n≤N) →
      (∑ n ∈ Q,omegaReciprocal n) ≤ C*(Real.log N)^(3/2:ℝ) := by
  classical
  obtain ⟨D,hD,hDerr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp ((3/2:ℝ)*D+9),Real.exp_pos _,?_⟩
  intro N hN Q hQ
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hfilter : P.filter (fun p : ℕ => (1:ℝ)<p ∧ (p:ℝ)≤N) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨hpN,hpp⟩ := Finset.mem_filter.mp hp
    exact ⟨by exact_mod_cast hpp.one_lt,by exact_mod_cast (Finset.mem_Icc.mp hpN).2⟩
  have hsum : (∑ n ∈ Q,omegaReciprocal n) =
      ∑ n ∈ Q,intervalOmegaWeight (3/2) 1 N n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [omegaReciprocal,intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,
      omegaIn_all_factors (hQ n hn).1 (hQ n hn).2]
  have hmass := interval_omega_moment_product (by norm_num : (0:ℝ)≤3/2)
    (by norm_num : (3/2:ℝ)≤3/2) 1 N N Q hQ
  have hprod := interval_euler_product_bound (by norm_num : (0:ℝ)≤3/2)
    (by norm_num : (3/2:ℝ)≤3/2) 1 N N
  change _ ≤ Real.exp ((∑ p ∈ P,(p:ℝ)⁻¹)+
    ((3/2:ℝ)-1)*(∑ p ∈ P.filter (fun p : ℕ => (1:ℝ)<p ∧ (p:ℝ)≤N),(p:ℝ)⁻¹)+9) at hprod
  rw [hfilter] at hprod
  have he : (∑ p ∈ P,(p:ℝ)⁻¹)=primeReciprocalLE N := by
    simp only [P,primeReciprocalLE,primesUpTo,Nat.floor_natCast]
  have herr := (abs_le.mp (hDerr N (by exact_mod_cast hN))).2
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  calc
    _ = _ := hsum
    _ ≤ _ := hmass.trans hprod
    _ ≤ Real.exp (((3/2:ℝ)*D+9)+(3/2:ℝ)*B N) := by
      apply Real.exp_le_exp.mpr
      rw [he]
      nlinarith
    _ = _ := by
      rw [Real.exp_add,Real.rpow_def_of_pos hlog]
      congr 1
      unfold B
      congr 1
      ring

end TotientAsymptotic

end

end OAI
