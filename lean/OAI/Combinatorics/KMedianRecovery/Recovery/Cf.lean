import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DisjointPool
import OAI.Combinatorics.KMedianRecovery.Recovery.FinishPhase

namespace OAI

namespace MetricKMedianRecovery.PriceBisection

end MetricKMedianRecovery.PriceBisection
namespace MetricKMedianRecovery.BitMachine.BinaryPriceRefine
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.Lookup.run
noncomputable def cf (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
noncomputable def cf_computes (k : ℕ) : PolyComputes (cf k) := extractPrefix_computes.comp (field_computes k)
noncomputable def contextPrice (x : List Bool) : List Bool := encode
  [cf 0 x,cf 1 x,cf 2 x,cf 3 x,discardPrefix x,cf 5 x,cf 6 x,cf 7 x,cf 8 x]
noncomputable def contextPrice_computes : PolyComputes contextPrice :=
  list_computes [cf 0,cf 1,cf 2,cf 3,discardPrefix,cf 5,cf 6,cf 7,cf 8] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨cf_computes _⟩ | exact ⟨discardPrefix_computes⟩)
lemma contextPrice_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam w : ℚ) : contextPrice (pairBits (BinaryPhaseFirst.context distance F Q v z lam,BinaryRational.encode w))=
      BinaryPhaseFirst.context distance F Q v z w := by
  simp only [contextPrice,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z : ℚ) (q n h : ℕ) (a b : ℚ) : List Bool := encode
  [List.replicate n true,List.replicate q true,BinaryPhaseFirst.context distance F Q v z 0,
    h.bits,BinaryRational.encode a,BinaryRational.encode b]
noncomputable def midpoint (x : List Bool) : ℚ :=
  (BinaryRational.decode (field 4 x)+BinaryRational.decode (field 5 x))/2
noncomputable def midpoint_computes : PolyComputes (fun x=>BinaryRational.encode (midpoint x)) :=
  RatOps.div (RatOps.add (RatOps.ofWords (field_computes 4)) (RatOps.ofWords (field_computes 5))) (RatOps.const 2)
noncomputable def query (x : List Bool) : List Bool :=
  pairBits (field 0 x,pairBits (field 1 x,contextPrice (pairBits (field 2 x,BinaryRational.encode (midpoint x)))))
noncomputable def query_computes : PolyComputes query :=
  (field_computes 0).pair ((field_computes 1).pair (((field_computes 2).pair midpoint_computes).comp contextPrice_computes))
lemma query_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z : ℚ) (q n h : ℕ) (a b : ℚ) : query (pack distance F Q v z q n h a b)=
      pairBits (List.replicate n true,pairBits (List.replicate q true,
        BinaryPhaseFirst.context distance F Q v z ((a+b)/2))) := by
  simp only [query,midpoint,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,contextPrice_pack]
noncomputable def countAt : List Bool → List Bool := BinaryPhaseCount.run ∘ query
noncomputable def countAt_computes : PolyComputes countAt := query_computes.comp BinaryPhaseCount.run_computes
noncomputable def run (x : List Bool) : List Bool :=
  if value (field 3 x) ≤ (countAt x).length then pairBits (BinaryRational.encode (midpoint x),field 5 x)
  else pairBits (field 4 x,BinaryRational.encode (midpoint x))
noncomputable def run_computes : PolyComputes run := by
  have hc := countAt_computes.comp UnaryResources.lengthBits_computes
  have ht := NatOps.le (field_computes 3) hc
  have hh := ht.cond (midpoint_computes.pair (field_computes 5)) ((field_computes 4).pair midpoint_computes)
  unfold run
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq,value_bits,decide_eq_true_eq] using hh
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z : ℚ) (q n h : ℕ) (a b : ℚ) :
    run (pack distance F Q v z q n h a b)=
      let I := PriceBisection.refine (fun lam=>RationalPhase.count distance F Q v lam q n) h (a,b)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  have hc : countAt (pack distance F Q v z q n h a b)=
      List.replicate (RationalPhase.count distance F Q v ((a+b)/2) q n) true := by
    rw [countAt,Function.comp_apply,query_pack,BinaryPhaseCount.run_pack]
  rw [run,hc]
  simp only [List.length_replicate,PriceBisection.refine,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,midpoint,BinaryRational.decode_encode]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryPriceRefine

end OAI
