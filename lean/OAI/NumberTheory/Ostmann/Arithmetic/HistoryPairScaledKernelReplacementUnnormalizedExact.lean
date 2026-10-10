import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementUnnormalizedExact
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementBounds

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacementUnnormalized
open HistoryPairKernelReplacement
open scoped BigOperators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open HistoryPairRepresentativeVariables PolynomialFlagReplacementFinite MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem shared_scaled_probability_error_le_exact (mixed : Bool) (h k : History l)
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
    (hw : ∀ x,(∀ i,x i∈S i) → ∀ b∈primes,0≤w x b ∧ w x b≤A)
    (hn : ∀ x,(∀ i,x i∈S i) → ∀ b∈primes,support x b=true →
      ¬∀i : Fiber h k r,
        leftRows h k hs ks r b
          (fun a=>(Function.update x (representativeMap h k r) (b:ℤ) a:ZMod b)) i=0 ∧
        rightRows h k hs ks r b
          (fun a=>(Function.update x (representativeMap h k r) (b:ℤ) a:ZMod b)) i=0) :
    (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*((b:ℝ)*
        |actualProbability mixed h k hs ks r b
          (Function.update x (representativeMap h k r) (b:ℤ))-symbolicKernel mixed h k hs ks r b|) else 0))) ≤
      (4*A)*(∑ j : Index h k r,
        (((polynomial h k hs ks r j).totalDegree : ℝ)*α*C^(Fintype.card (PairKey h k)-1)*Cnu+
          β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k))) := by
  classical
  have hw4 : ∀x,(∀i,x i∈S i) → ∀b∈primes,0≤4*w x b ∧ 4*w x b≤4*A := by
    intro x hxs b hb
    exact ⟨mul_nonneg (by norm_num) (hw x hxs b hb).1,
      mul_le_mul_of_nonneg_left (hw x hxs b hb).2 (by norm_num)⟩
  apply le_trans _ (HistoryPairFlagReplacementUnnormalized.shared_family_error_le_exact
    h k hs ks r S μ primes ν B α β (4*A) C Cnu hB hα hβ
    (mul_nonneg (by norm_num) hA) hC hCnu hμ hmass hatom hprime hν hνmass hνatom hx hy
    support (fun x b=>4*w x b) hw4)
  apply Finset.sum_le_sum
  intro x hxs
  have hxs' := Fintype.mem_piFinset.mp hxs
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _=>hμ i _ (hxs' i)))
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left _ (hν b hb)
  split_ifs with hm
  · have hbnd := mul_le_mul_of_nonneg_left
      (actualProbability_scaled_error_le mixed h k hs ks hroot r b (hprime b hb)
        (Function.update x (representativeMap h k r) (b:ℤ)) (hn x hxs' b hb hm))
      (hw x hxs' b hb).1
    convert hbnd using 1; ring
  · exact le_rfl

theorem shared_scaled_masked_probability_replacement_le_exact (mixed : Bool) (h k : History l)
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
    (hw : ∀ x,(∀ i,x i∈S i) → ∀ b∈primes,0≤w x b ∧ w x b≤A)
    (hn : ∀ x,(∀ i,x i∈S i) → ∀ b∈primes,support x b=true →
      ¬∀i : Fiber h k r,
        leftRows h k hs ks r b
          (fun a=>(Function.update x (representativeMap h k r) (b:ℤ) a:ZMod b)) i=0 ∧
        rightRows h k hs ks r b
          (fun a=>(Function.update x (representativeMap h k r) (b:ℤ) a:ZMod b)) i=0) :
    |(∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*((b:ℝ)*
        actualProbability mixed h k hs ks r b
          (Function.update x (representativeMap h k r) (b:ℤ))) else 0)))-
      (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*((b:ℝ)*
        symbolicKernel mixed h k hs ks r b) else 0)))| ≤
      (4*A)*(∑ j : Index h k r,
        (((polynomial h k hs ks r j).totalDegree : ℝ)*α*C^(Fintype.card (PairKey h k)-1)*Cnu+
          β*(max 0 (Real.log (envelope h k V B))/Real.log 2)*C^Fintype.card (PairKey h k))) := by
  classical
  have hid : (∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*((b:ℝ)*
        actualProbability mixed h k hs ks r b
          (Function.update x (representativeMap h k r) (b:ℤ))) else 0)))-(∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
      (∑ b∈primes,ν b*(if support x b then w x b*((b:ℝ)*
        symbolicKernel mixed h k hs ks r b) else 0))) =
      ∑ x∈Fintype.piFinset S,(∏ i,μ i (x i))*
        (∑ b∈primes,ν b*(if support x b then w x b*((b:ℝ)*
          (actualProbability mixed h k hs ks r b
          (Function.update x (representativeMap h k r) (b:ℤ))-symbolicKernel mixed h k hs ks r b)) else 0)) := by
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
  apply le_trans _ (shared_scaled_probability_error_le_exact mixed h k hs ks hroot r S μ primes ν
    B α β A C Cnu hB hα hβ hA hC hCnu hμ hmass hatom hprime hν hνmass hνatom hx hy support w hw hn)
  apply Finset.sum_le_sum
  intro x hxs
  have hxs' := Fintype.mem_piFinset.mp hxs
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _=>hμ i _ (hxs' i)))
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left _ (hν b hb)
  split_ifs
  · rw [abs_mul,abs_mul,abs_of_nonneg (hw x hxs' b hb).1,abs_of_nonneg (Nat.cast_nonneg b)]
  · simp only [abs_zero,le_refl]

end Ostmann.Arithmetic.HistoryPairKernelReplacementUnnormalized

end

end OAI
