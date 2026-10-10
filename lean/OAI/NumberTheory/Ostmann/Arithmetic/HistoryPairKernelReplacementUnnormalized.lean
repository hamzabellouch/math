import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlagReplacementUnnormalized
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacement

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacementUnnormalized
open HistoryPairKernelReplacement
open scoped BigOperators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open HistoryPairRepresentativeVariables PolynomialFlagReplacementFinite MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem shared_probability_error_le (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k)
    (S : PairKey h k → Finset ℤ) (μ : PairKey h k → ℤ → ℝ)
    (primes : Finset ℕ) (ν : ℕ → ℝ) (B α β A C Cnu : ℝ)
    (hB : 1≤B) (hα : 0≤α) (hβ : 0≤β) (hA : 0≤A) (hC : 0≤C) (hCnu : 0≤Cnu)
    (hμ : ∀ i a,a∈S i → 0≤μ i a) (hmass : ∀ i,∑ a∈S i,μ i a≤C)
    (hatom : ∀ i a,a∈S i → μ i a≤α)
    (hprime : ∀ b∈primes,b.Prime) (hν : ∀ b∈primes,0≤ν b)
    (hνmass : ∑ b∈primes,ν b≤Cnu) (hνatom : ∀ b∈primes,ν b≤β)
    (hx : ∀ a : Fin h.root.small.length ⊕ InternalKey h,∀ z∈S (leftMap h k (.inr a)),|(z:ℝ)|≤B)
    (hy : ∀ a : Fin k.root.small.length ⊕ InternalKey k,∀ z∈S (rightMap h k (.inr a)),|(z:ℝ)|≤B)
    (support : (PairKey h k → ℤ) → ℕ → Bool) (w : (PairKey h k → ℤ) → ℕ → ℝ)
    (hw : ∀ x,(∀ i,x i∈S i) → ∀ b∈primes,0≤w x b ∧ w x b≤A) :
    (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*
        |actualProbability mixed h k hs ks r b
          (Function.update x (representativeMap h k r) (b:ℤ))-
          symbolicKernel mixed h k hs ks r b| else 0))) ≤
      A*((2*Fintype.card (Fiber h k r)+(Fintype.card (Fiber h k r))^2:ℕ):ℝ)*
        ((4*degreeBudget h k:ℕ)*α*C^(Fintype.card (PairKey h k)-1)*Cnu+
          β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k)) := by
  classical
  apply le_trans _ (HistoryPairFlagReplacementUnnormalized.shared_family_error_le h k hs ks r S μ primes ν
    B α β A C Cnu hB hα hβ hA hC hCnu hμ hmass hatom hprime hν hνmass hνatom hx hy support w hw)
  apply Finset.sum_le_sum
  intro x hxs
  have hxs' := Fintype.mem_piFinset.mp hxs
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => hμ i _ (hxs' i)))
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left _ (hν b hb)
  split_ifs
  · exact mul_le_mul_of_nonneg_left
      (actualProbability_error_le mixed h k hs ks hroot r b (hprime b hb) _)
      (hw x hxs' b hb).1
  · exact le_rfl

theorem shared_masked_probability_replacement_le (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k)
    (S : PairKey h k → Finset ℤ) (μ : PairKey h k → ℤ → ℝ)
    (primes : Finset ℕ) (ν : ℕ → ℝ) (B α β A C Cnu : ℝ)
    (hB : 1≤B) (hα : 0≤α) (hβ : 0≤β) (hA : 0≤A) (hC : 0≤C) (hCnu : 0≤Cnu)
    (hμ : ∀ i a,a∈S i → 0≤μ i a) (hmass : ∀ i,∑ a∈S i,μ i a≤C)
    (hatom : ∀ i a,a∈S i → μ i a≤α)
    (hprime : ∀ b∈primes,b.Prime) (hν : ∀ b∈primes,0≤ν b)
    (hνmass : ∑ b∈primes,ν b≤Cnu) (hνatom : ∀ b∈primes,ν b≤β)
    (hx : ∀ a : Fin h.root.small.length ⊕ InternalKey h,∀ z∈S (leftMap h k (.inr a)),|(z:ℝ)|≤B)
    (hy : ∀ a : Fin k.root.small.length ⊕ InternalKey k,∀ z∈S (rightMap h k (.inr a)),|(z:ℝ)|≤B)
    (support : (PairKey h k → ℤ) → ℕ → Bool) (w : (PairKey h k → ℤ) → ℕ → ℝ)
    (hw : ∀ x,(∀ i,x i∈S i) → ∀ b∈primes,0≤w x b ∧ w x b≤A) :
    |(∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*
        actualProbability mixed h k hs ks r b
          (Function.update x (representativeMap h k r) (b:ℤ)) else 0)))-
      (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*
        symbolicKernel mixed h k hs ks r b else 0)))| ≤
      A*((2*Fintype.card (Fiber h k r)+(Fintype.card (Fiber h k r))^2:ℕ):ℝ)*
        ((4*degreeBudget h k:ℕ)*α*C^(Fintype.card (PairKey h k)-1)*Cnu+
          β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k)) := by
  classical
  have hid :
      (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
        (∑ b∈primes,ν b*(if support x b then w x b*
          actualProbability mixed h k hs ks r b
            (Function.update x (representativeMap h k r) (b:ℤ)) else 0)))-
      (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
        (∑ b∈primes,ν b*(if support x b then w x b*
          symbolicKernel mixed h k hs ks r b else 0))) =
      ∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
        (∑ b∈primes,ν b*(if support x b then w x b*
          (actualProbability mixed h k hs ks r b
            (Function.update x (representativeMap h k r) (b:ℤ))-
            symbolicKernel mixed h k hs ks r b) else 0)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [←mul_sub,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> ring
  rw [hid]
  apply (abs_product_prior_sum_le S μ primes ν hμ hν _).trans
  apply le_trans _ (shared_probability_error_le mixed h k hs ks hroot r S μ primes ν
    B α β A C Cnu hB hα hβ hA hC hCnu hμ hmass hatom hprime hν hνmass hνatom hx hy support w hw)
  apply Finset.sum_le_sum
  intro x hxs
  have hxs' := Fintype.mem_piFinset.mp hxs
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => hμ i _ (hxs' i)))
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left _ (hν b hb)
  split_ifs
  · rw [abs_mul,abs_of_nonneg (hw x hxs' b hb).1]
  · simp only [abs_zero,le_refl]

end Ostmann.Arithmetic.HistoryPairKernelReplacementUnnormalized

end

end OAI
