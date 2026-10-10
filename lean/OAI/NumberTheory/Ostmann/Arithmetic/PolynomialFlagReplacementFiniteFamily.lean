import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementFinite

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagReplacementFinite
open scoped BigOperators
open MvPolynomial

theorem weighted_restricted_flag_error_le_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℤ)
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀i a,a∈S i → 0 ≤ μ i a) (hmass : ∀i,∑a∈S i,μ i a=1)
    (hatom : ∀i a,a∈S i → μ i a ≤ α)
    (hprime : ∀b∈B,b.Prime) (hν : ∀b∈B,0 ≤ ν b) (hνmass : ∑b∈B,ν b=1)
    (hνatom : ∀b∈B,ν b ≤ β)
    (hsize : ∀x,(∀i,x i∈S i) → eval x P≠0 → Real.log |((eval x P:ℤ):ℝ)| ≤ H)
    (r : (ι → ℤ) → ℕ → Bool) (w : (ι → ℤ) → ℕ → ℝ)
    (hw : ∀x,(∀i,x i∈S i) → ∀b∈B,0 ≤ w x b ∧ w x b ≤ A) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*
      (∑b∈B,ν b*(if r x b then w x b*flagError P x b else 0))) ≤
      A*((P.totalDegree:ℝ)*α+β*(H/Real.log 2)) := by
  classical
  by_cases hP : P=0
  · subst P
    rw [identity_replacement_exact]
    have hlog : 0 ≤ Real.log (2:ℝ) := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
    positivity
  · exact weighted_restricted_flag_error_le P hP S μ B ν α β H A hα hβ hH hA
      hμ hmass hatom hprime hν hνmass hνatom hsize r w hw

theorem product_prior_sum_comm {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (D : Finset κ) (f : κ → (ι → ℤ) → ℕ → ℝ) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*(∑b∈B,ν b*(∑j∈D,f j x b))) =
      ∑j∈D,∑x∈Fintype.piFinset S,(∏i,μ i (x i))*(∑b∈B,ν b*f j x b) := by
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑x∈Fintype.piFinset S,∑j∈D,∑b∈B,(∏i,μ i (x i))*(ν b*f j x b) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem family_weighted_restricted_flag_error_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset κ) (P : κ → MvPolynomial ι ℤ)
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀i a,a∈S i → 0 ≤ μ i a) (hmass : ∀i,∑a∈S i,μ i a=1)
    (hatom : ∀i a,a∈S i → μ i a ≤ α)
    (hprime : ∀b∈B,b.Prime) (hν : ∀b∈B,0 ≤ ν b) (hνmass : ∑b∈B,ν b=1)
    (hνatom : ∀b∈B,ν b ≤ β)
    (hsize : ∀j∈D,∀x,(∀i,x i∈S i) → eval x (P j)≠0 → Real.log |((eval x (P j):ℤ):ℝ)| ≤ H)
    (r : (ι → ℤ) → ℕ → Bool) (w : (ι → ℤ) → ℕ → ℝ)
    (hw : ∀x,(∀i,x i∈S i) → ∀b∈B,0 ≤ w x b ∧ w x b ≤ A) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*
      (∑b∈B,ν b*(if r x b then w x b*(∑j∈D,flagError (P j) x b) else 0))) ≤
      A*(∑j∈D,(((P j).totalDegree:ℝ)*α+β*(H/Real.log 2))) := by
  classical
  have hi (x : ι → ℤ) (b : ℕ) :
      (if r x b then w x b*(∑j∈D,flagError (P j) x b) else 0) =
        ∑j∈D,(if r x b then w x b*flagError (P j) x b else 0) := by
    split_ifs <;> simp only [Finset.mul_sum,Finset.sum_const_zero]
  simp_rw [hi]
  rw [product_prior_sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact weighted_restricted_flag_error_le_all (P j) S μ B ν α β H A hα hβ hH hA
    hμ hmass hatom hprime hν hνmass hνatom (hsize j hj) r w hw

end Ostmann.Arithmetic.PolynomialFlagReplacementFinite

end

end OAI
