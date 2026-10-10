import OAI.NumberTheory.Jacobsthal.Estimates.SourceEdgeClasses

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem prime_sample_coprime (U : Finset ℕ) (hU : ∀ u ∈ U,Nat.Prime u) (h : ℕ) (sample : Fin h ↪ U) :
    Pairwise (fun i j => Nat.Coprime (sample i).val (sample j).val) := by
  intro i j hij
  apply (Nat.coprime_primes (hU _ (sample i).property) (hU _ (sample j).property)).mpr
  intro he
  exact hij (sample.injective (Subtype.ext he))

theorem small_prime_product_pos (small : Finset ℕ) (hsmall : ∀ p ∈ small,Nat.Prime p) :
    0 < ∏ p ∈ small,p := Finset.prod_pos (fun p hp => (hsmall p hp).pos)

theorem small_product_coprime_sample (small U : Finset ℕ)
    (hsmall : ∀ p ∈ small,Nat.Prime p) (hU : ∀ u ∈ U,Nat.Prime u)
    (hdisj : Disjoint small U) (h : ℕ) (sample : Fin h ↪ U) (i : Fin h) :
    Nat.Coprime (∏ p ∈ small,p) (sample i).val := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply (Nat.coprime_primes (hsmall p hp) (hU _ (sample i).property)).mpr
  intro he
  exact (Finset.disjoint_left.mp hdisj hp) (he.symm ▸ (sample i).property)

theorem sourceTestedSlopes_card_upper {ι : Type*} [Fintype ι] (p q0 M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (hp : ∀ i,Nat.Coprime p (u i)) (hq : ∀ i,Nat.Coprime q0 (u i)) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i)))
    (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((sourceTestedSlopes p q0 M0 u hp hq a b0 E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∑ v : ZMod M0,∏ i,((E v i).card : ℝ)/(u i : ℝ))+
        (M0 : ℝ)*((∏ i,u i : ℕ) : ℝ) := by
  rw [sourceTestedSlopes_eq_sampledSlopes]
  exact sampledSlopes_card_upper p M0 u _ _ E hU h0 hu

theorem distinct_prime_sample_slope_bound (U : Finset ℕ) (hU : ∀ u ∈ U,Nat.Prime u)
    (h : ℕ) (sample : Fin h ↪ U) (p q0 M0 : ℕ) [NeZero M0]
    (hp : ∀ u ∈ U,Nat.Coprime p u) (hq : ∀ u ∈ U,Nat.Coprime q0 u)
    (h0 : ∀ u ∈ U,Nat.Coprime M0 u) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i : Fin h,Finset (ZMod (sample i).val)) :
    ((sourceTestedSlopes p q0 M0 (fun i => (sample i).val)
      (fun i => hp _ (sample i).property) (fun i => hq _ (sample i).property) a b0 E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∑ v : ZMod M0,∏ i : Fin h,((E v i).card : ℝ)/((sample i).val : ℝ))+
        (M0 : ℝ)*((∏ i : Fin h,(sample i).val : ℕ) : ℝ) := by
  exact sourceTestedSlopes_card_upper p q0 M0 _ _ _ a b0 E
    (fun i => (hU _ (sample i).property).pos) (fun i => h0 _ (sample i).property)
    (prime_sample_coprime U hU h sample)

theorem mem_sourceTestedSlopes_of_same_cell {ι : Type*} [Fintype ι]
    (p q q0 M0 : ℕ) (u : ι → ℕ) (hp : ∀ i,Nat.Coprime p (u i))
    (hq : ∀ i,Nat.Coprime q (u i)) (hq0 : ∀ i,Nat.Coprime q0 (u i))
    (a : ℕ → ℤ) (b b0 s : ℤ) (E : ZMod M0 → ∀ i,Finset (ZMod (u i)))
    (hs : s ∈ Finset.Ico (0 : ℤ) (p : ℤ))
    (hqq : ∀ i,(q : ZMod (u i)) = (q0 : ZMod (u i)))
    (hbb : ∀ i,(b : ZMod (u i)) = (b0 : ZMod (u i)))
    (hE : ∀ i,sourceEdgeResidue p q (u i) (hp i) (hq i) (a (u i)) b s ∈ E (s : ZMod M0) i) :
    s ∈ sourceTestedSlopes p q0 M0 u hp hq0 a b0 E := by
  apply Finset.mem_filter.mpr
  refine ⟨hs,?_⟩
  intro i
  rw [← sourceEdgeResidue_of_same_cell p q q0 (u i) (hp i) (hq i) (hq0 i) (a (u i)) b b0 s (hqq i) (hbb i)]
  exact hE i

end ErdosInverseCRT

end

end Erdos970

end OAI
