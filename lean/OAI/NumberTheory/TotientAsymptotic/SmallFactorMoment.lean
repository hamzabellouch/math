import OAI.NumberTheory.TotientAsymptotic.IntervalMomentBound

namespace OAI

/-! A three-halves moment counting only prime factors at most S. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma small_factor_moment_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ S : ℝ, 2 ≤ S → ∀ Q : Finset ℕ, (∀ n ∈ Q,0 < n ∧ n ≤ N) →
    (∑ n ∈ Q,intervalOmegaWeight (3/2) 1 S n) ≤
      C*Real.log N*Real.exp (B S/2) := by
  classical
  obtain ⟨D,hD,herr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp ((3/2:ℝ)*D+9),Real.exp_pos _,?_⟩
  intro N hN S hS Q hQ
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hsub : P.filter (fun p : ℕ => (1:ℝ) < p ∧ (p:ℝ) ≤ S) ⊆ primesUpTo S := by
    intro p hp
    obtain ⟨hp,hpS⟩ := Finset.mem_filter.mp hp
    exact (primesUpTo_mem (by linarith)).mpr ⟨(Finset.mem_filter.mp hp).2,hpS.2⟩
  have hs : (∑ p ∈ P.filter (fun p : ℕ => (1:ℝ) < p ∧ (p:ℝ) ≤ S),(p:ℝ)⁻¹) ≤
      primeReciprocalLE S :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hn : (∑ p ∈ P,(p:ℝ)⁻¹) = primeReciprocalLE N := by
    simp only [P,primeReciprocalLE,primesUpTo,Nat.floor_natCast]
  have hnerr := (abs_le.mp (herr N (by exact_mod_cast hN))).2
  have hserr := (abs_le.mp (herr S hS)).2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ ∏ p ∈ P,(1-(if (1:ℝ) < p ∧ (p:ℝ) ≤ S then (3/2:ℝ) else 1)/(p:ℝ))⁻¹ :=
      interval_omega_moment_product (by norm_num) (by norm_num) 1 S N Q hQ
    _ ≤ Real.exp ((∑ p ∈ P,(p:ℝ)⁻¹)+
        ((3/2:ℝ)-1)*(∑ p ∈ P.filter (fun p : ℕ => (1:ℝ) < p ∧ (p:ℝ) ≤ S),(p:ℝ)⁻¹)+9) :=
      interval_euler_product_bound (by norm_num) (by norm_num) 1 S N
    _ ≤ Real.exp (((3/2:ℝ)*D+9)+B N+B S/2) := by
      apply Real.exp_le_exp.mpr
      rw [hn]
      linarith
    _ = _ := by
      rw [Real.exp_add,Real.exp_add]
      simp only [B,Real.exp_log hlog]

end TotientAsymptotic

end

end OAI
