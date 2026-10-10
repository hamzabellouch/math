import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerResources

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Trace
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySeed.rows Take.run Loop.run BinaryEllipsoidInitial.indices WordList.mapWith
noncomputable def rows (x : List Bool) : List Bool :=
  BinarySeed.rows (pairBits (encode [field 2 x,field 3 x],field 4 x))
noncomputable def rows_computes : PolyComputes rows :=
  ((cons_computes (field_computes 2) (cons_computes (field_computes 3) (const_computes []))).pair
    (field_computes 4)).comp BinarySeed.rows_computes
noncomputable def input (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 3 x,rows x]
noncomputable def input_computes : PolyComputes input :=
  cons_computes (field_computes 0) (cons_computes (field_computes 1)
    (cons_computes (field_computes 3) (cons_computes rows_computes (const_computes []))))
noncomputable def prefixBits (x : List Bool) : List Bool :=
  Take.run (pairBits (discardPrefix x,field 3 (extractPrefix x)))
noncomputable def prefixBits_computes : PolyComputes prefixBits :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 3))).comp Take.run_computes
noncomputable def atPrefix (x : List Bool) : List Bool := Loop.run
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),prefixBits x])
noncomputable def atPrefix_computes : PolyComputes atPrefix :=
  (cons_computes (extractPrefix_computes.comp (field_computes 0))
    (cons_computes (extractPrefix_computes.comp (field_computes 1))
      (cons_computes (extractPrefix_computes.comp (field_computes 2))
        (cons_computes prefixBits_computes (const_computes []))))).comp Loop.run_computes
noncomputable def run (x : List Bool) : List Bool :=
  mapWith atPrefix (pairBits (input x,BinaryEllipsoidInitial.indices (field 2 x++[true])))
noncomputable def run_computes : PolyComputes run :=
  (input_computes.pair (((field_computes 2).append (const_computes [true])).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes atPrefix_computes)
def pack {t b : ℕ} (cfg : List Bool) (m : ℕ) (seed : Fin t→Fin b→Bool) : List Bool :=
  encode [cfg,List.replicate m true,List.replicate t true,List.replicate b true,BinarySeed.raw (ds:=[t]) seed]
lemma input_pack {t b : ℕ} (cfg : List Bool) (m : ℕ) (seed : Fin t→Fin b→Bool) :
    input (pack cfg m seed)=Loop.runPack cfg m b (List.ofFn seed) := by
  have hr : rows (pack cfg m seed)=encode (List.ofFn (fun i=>List.ofFn (seed i))) := by
    simp only [rows,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    exact BinarySeed.rows_tensor seed
  rw [input,hr]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    Loop.runPack,List.map_ofFn,Function.comp_def]
lemma atPrefix_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (seeds : List (Fin b→Bool)) (j : ℕ) :
    atPrefix (pairBits (Loop.runPack (config δ D F S Δ P κ m M E J) m b seeds,j.bits))=
      BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b)
        (some RationalSampling.State.initial)) := by
  have hp : prefixBits (pairBits (Loop.runPack (config δ D F S Δ P κ m M E J) m b seeds,j.bits))=
      encode ((seeds.take j).map List.ofFn) := by
    simp only [prefixBits,extractPrefix_pairBits,discardPrefix_pairBits,Loop.runPack,field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Take.run_encode,List.map_take]
  rw [atPrefix,hp]
  simp only [extractPrefix_pairBits,Loop.runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact Loop.run_pack δ D F S Δ P κ m M E J b (seeds.take j)
lemma run_pack {n t b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (seed : Fin t→Fin b→Bool) :
    run (pack (config δ D F S Δ P κ m M E J) m seed)=encode (List.ofFn (fun j:Fin (t+1)=>
      BinarySamplingState.optionBits (((List.ofFn seed).take j.val).foldl (RationalSampling.next δ D F S Δ P κ m M E J b)
        (some RationalSampling.State.initial)))) := by
  rw [run,input_pack]
  have hi : field 2 (pack (config δ D F S Δ P κ m M E J) m seed)++[true]=List.replicate (t+1) true := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.replicate_add,List.replicate_one]
  rw [hi,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact atPrefix_pack δ D F S Δ P κ m M E J b (List.ofFn seed) j.val
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

end OAI
