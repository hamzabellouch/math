import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlagReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementUnnormalized

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairFlagReplacementUnnormalized
open scoped BigOperators
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryPairFlags HistoryPairRepresentativeVariables PolynomialFlagReplacementFinite MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem shared_family_error_le_exact (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k)
    (S : PairKey h k → Finset ℤ) (μ : PairKey h k → ℤ → ℝ)
    (primes : Finset ℕ) (ν : ℕ → ℝ) (B α β A C Cnu : ℝ)
    (hB : 1≤B) (hα : 0≤α) (hβ : 0≤β) (hA : 0≤A) (hC : 0≤C) (hCnu : 0≤Cnu)
    (hμ : ∀i a,a∈S i→0≤μ i a) (hmass : ∀i,∑a∈S i,μ i a≤C)
    (hatom : ∀i a,a∈S i→μ i a≤α)
    (hprime : ∀b∈primes,b.Prime) (hν : ∀b∈primes,0≤ν b)
    (hνmass : ∑b∈primes,ν b≤Cnu) (hνatom : ∀b∈primes,ν b≤β)
    (hx : ∀a : Fin h.root.small.length ⊕ InternalKey h,
      ∀z∈S (leftMap h k (.inr a)),|(z:ℝ)|≤B)
    (hy : ∀a : Fin k.root.small.length ⊕ InternalKey k,
      ∀z∈S (rightMap h k (.inr a)),|(z:ℝ)|≤B)
    (support : (PairKey h k → ℤ) → ℕ → Bool) (w : (PairKey h k → ℤ) → ℕ → ℝ)
    (hw : ∀x,(∀i,x i∈S i)→∀b∈primes,0≤w x b∧w x b≤A) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*
      (∑b∈primes,ν b*(if support x b then w x b*
        (∑j : Index h k r,flagError (polynomial h k hs ks r j)
          (Function.update x (representativeMap h k r) (b:ℤ)) b) else 0))) ≤
      A*(∑j : Index h k r, (((polynomial h k hs ks r j).totalDegree:ℝ)*α*
        C^(Fintype.card (PairKey h k)-1)*Cnu+
        β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k))) := by
  classical
  simp_rw [HistoryPairFlagReplacement.shared_flagError_eq]
  exact PolynomialFlagReplacementUnnormalized.family_weighted_restricted_flag_error_le
    Finset.univ (polynomial h k hs ks r) S μ primes ν
    α β (max 0 (Real.log (envelope h k V B))) A C Cnu
    hα hβ (le_max_left _ _) hA hC hCnu hμ hmass hatom hprime hν hνmass hνatom
    (fun j _ x hxs hn => (polynomial_integer_log_bound h k hs ks r j x hB
      (fun a => hx a _ (hxs _)) (fun a => hy a _ (hxs _)) hn).trans (le_max_right _ _))
    support w hw

theorem shared_family_error_le (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k)
    (S : PairKey h k → Finset ℤ) (μ : PairKey h k → ℤ → ℝ)
    (primes : Finset ℕ) (ν : ℕ → ℝ) (B α β A C Cnu : ℝ)
    (hB : 1≤B) (hα : 0≤α) (hβ : 0≤β) (hA : 0≤A) (hC : 0≤C) (hCnu : 0≤Cnu)
    (hμ : ∀i a,a∈S i→0≤μ i a) (hmass : ∀i,∑a∈S i,μ i a≤C)
    (hatom : ∀i a,a∈S i→μ i a≤α)
    (hprime : ∀b∈primes,b.Prime) (hν : ∀b∈primes,0≤ν b)
    (hνmass : ∑b∈primes,ν b≤Cnu) (hνatom : ∀b∈primes,ν b≤β)
    (hx : ∀a : Fin h.root.small.length ⊕ InternalKey h,
      ∀z∈S (leftMap h k (.inr a)),|(z:ℝ)|≤B)
    (hy : ∀a : Fin k.root.small.length ⊕ InternalKey k,
      ∀z∈S (rightMap h k (.inr a)),|(z:ℝ)|≤B)
    (support : (PairKey h k → ℤ) → ℕ → Bool) (w : (PairKey h k → ℤ) → ℕ → ℝ)
    (hw : ∀x,(∀i,x i∈S i)→∀b∈primes,0≤w x b∧w x b≤A) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*
      (∑b∈primes,ν b*(if support x b then w x b*
        (∑j : Index h k r,flagError (polynomial h k hs ks r j)
          (Function.update x (representativeMap h k r) (b:ℤ)) b) else 0))) ≤
      A*((2*Fintype.card (Fiber h k r)+(Fintype.card (Fiber h k r))^2:ℕ):ℝ)*
        (((4*degreeBudget h k:ℕ):ℝ)*α*C^(Fintype.card (PairKey h k)-1)*Cnu+
          β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k)) := by
  classical
  apply (shared_family_error_le_exact h k hs ks r S μ primes ν B α β A C Cnu
    hB hα hβ hA hC hCnu hμ hmass hatom hprime hν hνmass hνatom hx hy support w hw).trans
  calc
    _ ≤ A*(∑_j : Index h k r, (((4*degreeBudget h k:ℕ):ℝ)*α*
        C^(Fintype.card (PairKey h k)-1)*Cnu+
        β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro j _
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ hCnu
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hC _)
      apply mul_le_mul_of_nonneg_right _ hα
      exact_mod_cast polynomial_degree h k hs ks r j
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,index_card]
      ring

end Ostmann.Arithmetic.HistoryPairFlagReplacementUnnormalized

end

end OAI
