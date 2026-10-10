import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryEnumeration

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] run
noncomputable def replaceState (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,field 0 (discardPrefix x),src 6 x,src 7 x,src 8 x,src 9 x]
noncomputable def replaceState_computes : PolyComputes replaceState := list_computes
  [src 0,src 1,src 2,src 3,src 4,field 0 ∘ discardPrefix,src 6,src 7,src 8,src 9] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨discardPrefix_computes.comp (field_computes 0)⟩)
noncomputable def atOption (d : ℕ) (x : List Bool) : List Bool :=
  if decide (discardPrefix x=[]) then src 3 x else run d (replaceState x)
noncomputable def atOption_computes (d : ℕ) : PolyComputes (atOption d) := by
  unfold atOption
  exact (discardPrefix_computes.comp isEmpty_computes).cond (src_computes 3)
    (replaceState_computes.comp (run_computes d))
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s0 s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool)
lemma replaceState_pack : replaceState (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (some s)))=pack δ D F S Δ s m extra raw := by
  simp only [replaceState,src,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    pack,BinarySamplingState.optionBits,Option.toList_some,List.map_cons,List.map_nil,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma atOption_none (d : ℕ) : atOption d (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (n:=n) none))=BinaryFinSet.encode S := by
  rw [atOption,discardPrefix_pairBits]
  change (if decide (([]:List Bool)=[]) then src 3 _ else _) = _
  simp only [decide_true,ite_true]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma atOption_some (d : ℕ) : atOption d (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (some s)))=run d (pack δ D F S Δ s m extra raw) := by
  have h : BinarySamplingState.optionBits (some s)≠[] := by
    simp [BinarySamplingState.optionBits,WordList.encode,WordList.cons,pairBits]
  rw [atOption,discardPrefix_pairBits]
  simp only [h,decide_false,Bool.false_eq_true,ite_false,replaceState_pack]
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
