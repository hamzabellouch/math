import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralDispatchLaws
import OAI.Combinatorics.KMedianRecovery.Strictness.MetricSurplus

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace Dsp
abbrev pack := @BinaryIntegralDispatch.pack
noncomputable abbrev run := BinaryIntegralDispatch.run
noncomputable abbrev budget := BinaryIntegralDispatch.budget
end Dsp
variable {n : ℕ}
noncomputable def src (j : ℕ) : List Bool→ List Bool := field j ∘ extractPrefix
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def less (x : List Bool) : List Bool := (BinaryArithmetic.value (src 5 x)-BinaryArithmetic.value (discardPrefix x)).bits
noncomputable def less_computes : PolyComputes less := NatOps.sub (src_computes 5) discardPrefix_computes
noncomputable def surplusInput (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,less x,discardPrefix x]
noncomputable def surplusInput_computes : PolyComputes surplusInput := list_computes
  [src 0,src 1,src 2,src 3,src 4,less,discardPrefix] (by
    intro f hf; refine Classical.choice ?_; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨less_computes⟩ | exact ⟨discardPrefix_computes⟩)
noncomputable def surplus (v : ℚ) (C : ℕ) : List Bool→ List Bool := BinaryMetricSurplus.run v C ∘ surplusInput
noncomputable def surplus_computes (v : ℚ) (C : ℕ) : PolyComputes (surplus v C) :=
  surplusInput_computes.comp (BinaryMetricSurplus.run_computes v C)
noncomputable def surplusCalls (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  mapWith (surplus v C) (pairBits (x,BinaryIntegralDispatch.ranks x))
attribute [local irreducible] mapWith
noncomputable def surplusCalls_computes (v : ℚ) (C : ℕ) : PolyComputes (surplusCalls v C) :=
  PolyComputes.comp (f := fun input=>pairBits (input,BinaryIntegralDispatch.ranks input))
    (g := mapWith (surplus v C))
    (id_computes.pair BinaryIntegralDispatch.ranks_computes) (mapWith_computes (surplus_computes v C))
noncomputable def candidates (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  cons (Dsp.run Q d x) (surplusCalls v C x)
noncomputable def candidates_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidates v C Q d) :=
  cons_computes (BinaryIntegralDispatch.run_computes Q d) (surplusCalls_computes v C)
noncomputable def runInput (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 2 x,field 3 x,BinaryIntegralDispatch.start x,field 5 x,candidates v C Q d x]
noncomputable def runInput_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (runInput v C Q d) :=
  list_computes [field 0,field 2,field 3,BinaryIntegralDispatch.start,field 5,candidates v C Q d] (by
    intro f hf; refine Classical.choice ?_; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨BinaryIntegralDispatch.start_computes⟩ | exact ⟨candidates_computes v C Q d⟩)
noncomputable def run (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→ List Bool :=
  BinarySanitizedBest.run ∘ runInput v C Q d
noncomputable def run_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run v C Q d) :=
  (runInput_computes v C Q d).comp BinarySanitizedBest.run_computes
lemma surplusInput_pack (δ : Fin n→ Fin n→ℚ) (D F : Finset (Fin n)) (Δ k L : ℕ) (g raw : List Bool) :
    surplusInput (pairBits (Dsp.pack δ D F Δ k g raw,L.bits))=BinaryMetricSurplus.pack δ D F Δ (k-L) L := by
  simp only [surplusInput,less,src,Dsp.pack,BinaryIntegralDispatch.pack,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryArithmetic.value_bits,BinaryMetricSurplus.pack]
lemma surplus_pack (v : ℚ) (C : ℕ) (δ : Fin n→ Fin n→ℚ) (D F : Finset (Fin n)) (Δ k L : ℕ) (g raw : List Bool) :
    surplus v C (pairBits (Dsp.pack δ D F Δ k g raw,L.bits))=
      BinaryMetricSurplus.run v C (BinaryMetricSurplus.pack δ D F Δ (k-L) L) := by
  rw [surplus,Function.comp_apply,surplusInput_pack]
noncomputable def words (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List (List Bool) :=
  Dsp.run Q d (Dsp.pack δ D F Δ k g raw)::
    List.ofFn (fun L:Fin (F.card+1)=>surplus v C (pairBits (Dsp.pack δ D F Δ k g raw,L.val.bits)))
lemma candidates_pack (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) :
    candidates v C Q d (Dsp.pack δ D F Δ k g raw)=encode (words v C Q d δ D F Δ k g raw) := by
  rw [candidates,surplusCalls,BinaryIntegralDispatch.ranks_pack,mapWith_ofFn]
  rfl
noncomputable def output (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : Finset (Fin n) :=
  BinarySanitizedBest.output δ D F S k (words v C Q d δ D F Δ k g raw)
lemma run_output (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S) :
    run v C Q d (Dsp.pack δ D F Δ k g raw)=BinaryFinSet.encode (output v C Q d δ D F S Δ k g raw) := by
  rw [run,Function.comp_apply,runInput,candidates_pack,BinaryIntegralDispatch.start_pack,hs]
  simp only [Dsp.pack,BinaryIntegralDispatch.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinarySanitizedBest.run_pack δ D F S k _
lemma output_feasible (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) :
    output v C Q d δ D F S Δ k g raw⊆F ∧ (output v C Q d δ D F S Δ k g raw).Nonempty ∧
      (output v C Q d δ D F S Δ k g raw).card≤ k :=
  BinarySanitizedBest.output_feasible δ D F S k _ hSF hS hSk
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
attribute [local irreducible] output words surplus BinaryIntegralDispatch.output BinaryIntegralDispatch.run
lemma cost_le_start (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) :
    realCost D (output v C Q d δ D F S Δ k g raw)≤ realCost D S := by
  rw [output]
  exact BinarySanitizedBest.realCost_le_self δ hδ D F S k _ hSF hS hSk
lemma cost_le_dispatch (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S) :
    realCost D (output v C Q d δ D F S Δ k g raw)≤
      realCost D (BinaryIntegralDispatch.output Q d δ D F S Δ k g raw) := by
  rw [output]
  have hh:=BinaryIntegralDispatch.output_feasible Q d δ D F S Δ k g raw hSF hS hSk
  apply BinarySanitizedBest.realCost_le_good δ hδ D F S k _ hSF hS hSk _ hh.1 hh.2.1 hh.2.2
  rw [←BinaryIntegralDispatch.run_output Q d δ D F S Δ k g raw hs,words]
  exact List.mem_cons_self
lemma cost_le_surplus (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) (L : ℕ) (hL : L≤ F.card)
    (U : Finset (Fin n)) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤ k)
    (hu : BinaryMetricSurplus.run v C (BinaryMetricSurplus.pack δ D F Δ (k-L) L)=BinaryFinSet.encode U) :
    realCost D (output v C Q d δ D F S Δ k g raw)≤ realCost D U := by
  rw [output]
  apply BinarySanitizedBest.realCost_le_good δ hδ D F S k _ hSF hS hSk U hUF hU hUk
  rw [words]
  apply List.mem_cons_of_mem
  have he:=surplus_pack v C δ D F Δ k L g raw
  rw [hu] at he
  exact List.mem_ofFn.mpr ⟨⟨L,Nat.lt_succ_of_le hL⟩,he⟩
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
