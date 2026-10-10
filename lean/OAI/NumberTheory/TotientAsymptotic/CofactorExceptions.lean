import OAI.NumberTheory.TotientAsymptotic.CofactorDiscard
import OAI.NumberTheory.TotientAsymptotic.CanonicalCoverage

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def cofactorExceptionValues (x : ℝ) (H : ℕ) : Finset ℕ :=
  (totientValues x).filter (fun v => ∃ n : ℕ, 0<n ∧ n.totient=v ∧
    extractedStructureCondition x (P H) n ∧ x^(9/10 : ℝ) ≤ fordPrime n 0 ∧
    Real.exp (2*bandScale x (L x H))<Real.log (fordCofactor n (L x H+1)))

theorem cofactor_exception_count (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput)
    (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        ((cofactorExceptionValues x H).card : ℝ) ≤ ε H*tupleNormalization x := by
  obtain ⟨ε,hε,hbound⟩ := oversized_cofactor_count hbox hren hmertens
  refine ⟨ε,hε,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with H hH hH2
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H),eventually_ge_atTop (0 : ℝ)] with x hx hm hx0
  have hL : 0<L x H := by have := P_lt_self hH2; unfold L; omega
  let E := cofactorExceptionValues x H
  have hex (v : {v // v ∈ E}) : ∃ n : ℕ, 0<n ∧ n.totient=v.1 ∧
      extractedStructureCondition x (P H) n ∧ x^(9/10 : ℝ) ≤ fordPrime n 0 ∧
      Real.exp (2*bandScale x (L x H))<Real.log (fordCofactor n (L x H+1)) :=
    (Finset.mem_filter.mp v.2).2
  choose n hn hφ hs hp ha using hex
  let F : {v // v ∈ E} → RemainderDatum (L x H) × ℕ :=
    fun v => (fordRemainder x H (n v),fordPrime (n v) 0)
  let S := E.attach.image F
  have hreal (v : {v // v ∈ E}) : wholePreimage (F v).2 (F v).1=n v :=
    fordRemainder_factorization (hn v)
      (fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) (hs v).2.1))
  have hS : ∀ q ∈ S, IsUntruncatedRemainder x H q.1 ∧ q.2.Prime ∧
      x^(9/10 : ℝ) ≤ q.2 ∧ ((wholePreimage q.2 q.1).totient : ℝ) ≤ x ∧
      Real.exp (2*bandScale x (L x H))<Real.log q.1.cofactor := by
    intro q hq
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨fordRemainder_untruncated hL (hs v),?_,hp v,?_,ha v⟩
    · exact fordPrime_prime (lt_of_le_of_lt (Nat.zero_le _) (fordPrime_index_of_doubleLog_pos
        (lt_trans (by norm_num) (hs v).2.1)))
    · rw [hreal v,hφ v]
      exact (Nat.cast_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp v.2).1).1).2).trans
        (Nat.floor_le hx0)
  have hsub : E ⊆ S.image (fun q => (wholePreimage q.2 q.1).totient) := by
    intro v hv
    let v' : {v // v ∈ E} := ⟨v,hv⟩
    refine Finset.mem_image.mpr ⟨F v',Finset.mem_image.mpr ⟨v',Finset.mem_attach _ _,rfl⟩,?_⟩
    rw [hreal v',hφ v']
  exact (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)).trans (hx S hS)

end TotientAsymptotic

end

end OAI
