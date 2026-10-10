import OAI.NumberTheory.JointDickman.Amplification.CandidateScalarIdentity

namespace OAI

/-! # Recovering the unique additive coefficient in the candidate kernel -/

namespace JointDickman
open Finset

open Classical in
noncomputable def regularArithmeticScalar (B L j : ℕ) (τ C : ℝ) (T : ℕ)
    (c b a : ℕ) : ℝ :=
  if b.Coprime a ∧ RegularPrimeSet B L τ C (coefficientPrimeSet B c) then
    amplificationScalarWeight B j T c b a else 0

open Classical in
theorem regularCandidateScalar_eq_sum {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T)
    (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    {i t : Fin M} (hit : i < t) {A D : Finset ℕ}
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T) :
    regularCandidateScalar B L T H τ C ((i,t),(A,D)) =
      ∑ c ∈ Ioc 0 V, regularArithmeticScalar B L (t.val-i.val) τ C T c
        (∏ p ∈ A,p) (∏ p ∈ D,p) := by
  have hj : 0 < candidateLag ((i,t),(A,D)) := Nat.sub_pos_of_lt hit
  symm
  by_cases ha : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · rcases ha with ⟨_,_,_,hq,he,_,_,_,_,_,_,hqhi,_,_,_,_⟩
    have hmem : candidateQuotient ((i,t),(A,D)) ∈ Ioc 0 V := by
      refine mem_Ioc.mpr ⟨hq,?_⟩
      apply le_trans _ hV
      apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
      rw [← Real.exp_log (by exact_mod_cast hq : (0 : ℝ) < candidateQuotient ((i,t),(A,D)))]
      exact Real.exp_le_exp.mpr hqhi
    rw [sum_eq_single (candidateQuotient ((i,t),(A,D)))]
    · exact (regularCandidateScalar_eq_of_relation hB hT hq hit hH hjT he).symm
    · intro c hc hne
      by_contra hn
      have hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
        by_contra hp
        exact hn (by simp only [regularArithmeticScalar,ite_eq_right hp])
      have hw : amplificationScalarWeight B (t.val-i.val) T c
          (∏ p ∈ A,p) (∏ p ∈ D,p) ≠ 0 := by
        simpa only [regularArithmeticScalar,ite_eq_left hp] using hn
      have hec := (amplificationScalarWeight_support hB hT (mem_Ioc.mp hc).1 hw).1
      exact hne (candidateQuotient_of_relation hj hec).symm
    · intro hnot
      exact False.elim (hnot hmem)
  · rw [regularCandidateScalar,ite_eq_right ha]
    apply sum_eq_zero
    intro c hc
    by_cases hp : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c)
    · rw [regularArithmeticScalar,ite_eq_left hp]
      by_contra hw
      exact ha (candidateAdmissible_of_scalar hB hT (mem_Ioc.mp hc).1 hit hH hjT hw hp.1 hp.2)
    · exact ite_eq_right hp

end JointDickman

end OAI
