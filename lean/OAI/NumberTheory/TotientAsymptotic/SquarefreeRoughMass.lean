import OAI.NumberTheory.TotientAsymptotic.SquarefreeIntervalMass

namespace OAI

/-! The initial rough cofactor contributes a ratio of logarithms. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem squarefree_rough_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ U V : ℝ,
    2 ≤ U → U ≤ V → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,Squarefree n ∧ ∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log V/Real.log U := by
  obtain ⟨D,hD,hbound⟩ := prime_interval_upper_bounded_error
  refine ⟨Real.exp D,Real.exp_pos D,?_⟩
  intro U V hU hUV Q hQ
  let S := (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))
  have hV0 : 0 ≤ V := by linarith
  have hm := squarefree_reciprocal_moment S Q (c:=1) (by norm_num) (by
    intro n hn
    refine ⟨(hQ n hn).1,?_⟩
    intro p hp
    have hp' : p ∈ n.primeFactorsList := List.mem_toFinset.mp hp
    have hh := (hQ n hn).2 p hp'
    exact Finset.mem_filter.mpr ⟨(primesUpTo_mem hV0).mpr
      ⟨Nat.prime_of_mem_primeFactorsList hp',hh.2⟩,hh.1⟩)
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlogV : 0 < Real.log V := Real.log_pos (by linarith)
  calc
    _ ≤ Real.exp (∑ p ∈ S,(p:ℝ)⁻¹) := by simpa only [one_pow,one_div,one_mul] using hm
    _ ≤ Real.exp (B V-B U+D) := Real.exp_le_exp.mpr (hbound U V hU hUV)
    _ = _ := by
      rw [Real.exp_add,Real.exp_sub]
      simp only [B,Real.exp_log hlogV,Real.exp_log hlogU]
      ring

end TotientAsymptotic

end

end OAI
