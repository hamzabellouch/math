import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryAll

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList Completion Sampling.Comparison FiniteSampling
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] anchor BinaryMetricAnchor.run BinaryIntegralRecovery.Guesses.run recoveryParams demand budget
variable {n : ℕ}
lemma params_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    recoveryParams (pairBits (pack δ D F Δ k g raw,r.bits))=BinarySampler.Parameters.pack δ D F S Δ 0 0 := by
  rw [recoveryParams,anchor_pack,hs]
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinarySampler.Parameters.pack]
lemma bare_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    bare (pairBits (pack δ D F Δ k g raw,r.bits))=R.pack δ D F S Δ g [] := by
  rw [bare,params_pack δ D F S Δ k g raw r hs]
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,R.pack,BinaryIntegralRecovery.Fair.pack]
lemma demand_length (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    (demand Q (pairBits (pack δ D F Δ k g raw,r.bits))).length=(R.budget Q).eval (R.pack δ D F S Δ g []).length := by
  rw [demand,Function.comp_apply,bare_pack δ D F S Δ k g raw r hs,(counter Q).word_length]
lemma callInput_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    callInput Q (pairBits (pack δ D F Δ k g raw,r.bits))=R.pack δ D F S Δ g
      (raw.take ((R.budget Q).eval (R.pack δ D F S Δ g []).length)) := by
  rw [callInput,params_pack δ D F S Δ k g raw r hs,cutRaw,UnaryResources.lengthBits_eq,
    demand_length Q δ D F S Δ k g raw r hs]
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,RawTake.run_pack,R.pack,BinaryIntegralRecovery.Fair.pack]
lemma call_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    call Q d (pairBits (pack δ D F Δ k g raw,r.bits))=R.run Q d (R.pack δ D F S Δ g
      (raw.take ((R.budget Q).eval (R.pack δ D F S Δ g []).length))) := by
  rw [call,Function.comp_apply,callInput_pack Q δ D F S Δ k g raw r hs]
lemma demand_bound (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g : List Bool) (r : ℕ) (hr : r≤F.card)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    (R.budget Q).eval (R.pack δ D F S Δ g []).length≤(budget Q).eval (pack δ D F Δ k g []).length := by
  have hm : demand Q (pairBits (pack δ D F Δ k g [],r.bits))∈
      List.ofFn (fun j:Fin (F.card+1)=>demand Q (pairBits (pack δ D F Δ k g [],j.val.bits))) :=
    List.mem_ofFn.mpr ⟨⟨r,Nat.lt_succ_of_le hr⟩,rfl⟩
  have hb:=length_member_le_encode hm
  rw [demand_length Q δ D F S Δ k g [] r hs] at hb
  have he : demands Q (pack δ D F Δ k g [])=encode
      (List.ofFn (fun j:Fin (F.card+1)=>demand Q (pairBits (pack δ D F Δ k g [],j.val.bits)))) := by
    rw [demands,ranks_pack,mapWith_ofFn]
  rw [←he] at hb
  exact hb.trans (by simpa only [budget] using (demands_computes Q).length_bound (pack δ D F Δ k g []))
noncomputable def output (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : Finset (Fin n) :=
  BinarySanitizedBest.output δ D F S k (words Q d δ D F Δ k g raw)
lemma run_output (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S) :
    run Q d (pack δ D F Δ k g raw)=BinaryFinSet.encode (output Q d δ D F S Δ k g raw) := by
  rw [run,Function.comp_apply,runInput,calls_pack,start_pack,hs]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinarySanitizedBest.run_pack δ D F S k _
lemma output_feasible (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output Q d δ D F S Δ k g raw⊆F ∧ (output Q d δ D F S Δ k g raw).Nonempty ∧
      (output Q d δ D F S Δ k g raw).card≤k :=
  BinarySanitizedBest.output_feasible δ D F S k _ hSF hS hSk
variable [PseudoMetricSpace (Fin n)]
lemma cost_le_start (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    realCost D (output Q d δ D F S Δ k g raw)≤realCost D S :=
  BinarySanitizedBest.realCost_le_self δ hδ D F S k _ hSF hS hSk
lemma cost_le_call (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) (r : ℕ) (hr : r≤F.card)
    (U : Finset (Fin n)) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k)
    (hu : call Q d (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryFinSet.encode U) :
    realCost D (output Q d δ D F S Δ k g raw)≤realCost D U := by
  apply BinarySanitizedBest.realCost_le_good δ hδ D F S k _ hSF hS hSk U hUF hU hUk
  rw [←hu]
  exact List.mem_ofFn.mpr ⟨⟨r,Nat.lt_succ_of_le hr⟩,rfl⟩
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
