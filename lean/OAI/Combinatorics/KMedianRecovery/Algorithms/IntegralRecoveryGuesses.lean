import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryAmplified
import OAI.Combinatorics.KMedianRecovery.Algorithms.CandidateSanitize

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Repeat.FiniteTape.run BinarySanitizedBest.run BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
noncomputable def costWord (x : List Bool) : List Bool := RepeatedAppend.copies (Count.run (src 2 x)).length
  (BinarySampler.Parameters.unary 5 (extractPrefix x))
noncomputable def costWord_computes : PolyComputes costWord := UnaryResources.copy_computes
  ((src_computes 2).comp Count.run_computes) (extractPrefix_computes.comp (BinarySampler.Parameters.unary_computes 5))
noncomputable def costRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (costWord x++[true])
noncomputable def costRange_computes : PolyComputes costRange :=
  (costWord_computes.append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def countRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (src 1 x++[true])
noncomputable def countRange_computes : PolyComputes countRange :=
  ((src_computes 1).append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def choices (x : List Bool) : List Bool := cross (pairBits (costRange x,countRange x))
noncomputable def choices_computes : PolyComputes choices := (costRange_computes.pair countRange_computes).comp cross_computes
noncomputable def source (j : ℕ) : List Bool→List Bool := src j ∘ extractPrefix
noncomputable def source_computes (j : ℕ) : PolyComputes (source j) := extractPrefix_computes.comp (src_computes j)
noncomputable def price (x : List Bool) : List Bool := BinaryRational.natWords (extractPrefix (discardPrefix x))
noncomputable def price_computes : PolyComputes price :=
  (discardPrefix_computes.comp extractPrefix_computes).comp BinaryRational.natWords_computes
noncomputable def count (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def count_computes : PolyComputes count := discardPrefix_computes.comp discardPrefix_computes
noncomputable def atParams (x : List Bool) : List Bool := encode
  [source 0 x,source 1 x,source 2 x,source 3 x,source 4 x,source 5 x,price x,count x]
noncomputable def atParams_computes : PolyComputes atParams := list_computes
  [source 0,source 1,source 2,source 3,source 4,source 5,price,count] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨source_computes _⟩ | exact ⟨price_computes⟩ | exact ⟨count_computes⟩)
noncomputable def atInput (x : List Bool) : List Bool := pairBits (atParams x,pairBits
  (extra (extractPrefix x),Fair.raw (extractPrefix x)))
noncomputable def atInput_computes : PolyComputes atInput := atParams_computes.pair
  ((extractPrefix_computes.comp extra_computes).pair (extractPrefix_computes.comp Fair.raw_computes))
noncomputable def atChoice (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := Repeat.FiniteTape.run Q d ∘ atInput
noncomputable def atChoice_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (atChoice Q d) :=
  atInput_computes.comp (Repeat.FiniteTape.run_computes Q d)
noncomputable def candidateWords (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (atChoice Q d) (pairBits (x,choices x))
attribute [local irreducible] mapWith
noncomputable def candidateWords_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidateWords Q d) :=
  PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atChoice Q d))
    (id_computes.pair choices_computes) (mapWith_computes (atChoice_computes Q d))
noncomputable def sizeWord (x : List Bool) : List Bool := UnaryResources.lengthBits (Count.run (src 4 x))
noncomputable def sizeWord_computes : PolyComputes sizeWord :=
  ((src_computes 4).comp Count.run_computes).comp UnaryResources.lengthBits_computes
noncomputable def runInput (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [src 0 x,src 2 x,src 3 x,src 4 x,sizeWord x,candidateWords Q d x]
attribute [local irreducible] sizeWord candidateWords
noncomputable def runInput_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (runInput Q d) := list_computes
  [src 0,src 2,src 3,src 4,sizeWord,candidateWords Q d] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨sizeWord_computes⟩ | exact ⟨candidateWords_computes Q d⟩)
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := BinarySanitizedBest.run ∘ runInput Q d
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (runInput_computes Q d).comp BinarySanitizedBest.run_computes
variable {n : ℕ}
abbrev pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) : List Bool :=
  Fair.pack δ D F S Δ 0 0 g raw
lemma src_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) (j : ℕ) :
    src j (pack δ D F S Δ g raw)=field j (BinarySampler.Parameters.pack δ D F S Δ 0 0) := by
  simp only [src,pack,Fair.pack,Function.comp_apply,extractPrefix_pairBits]
lemma ranges_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    costRange (pack δ D F S Δ g raw)=encode (List.ofFn (fun p:Fin (D.card*Δ+1)=>p.val.bits)) ∧
    countRange (pack δ D F S Δ g raw)=encode (List.ofFn (fun m:Fin (n+1)=>m.val.bits)) := by
  have hd : BinarySampler.Parameters.unary 5 (extractPrefix (pack δ D F S Δ g raw))=List.replicate Δ true := by
    simp only [pack,Fair.pack,extractPrefix_pairBits]
    exact (BinarySampler.Parameters.unary_pack δ D F S Δ 0 0 (Nat.zero_le n) hΔ).2
  have hc : costWord (pack δ D F S Δ g raw)=List.replicate (D.card*Δ) true := by
    rw [costWord,hd,src_pack]
    simp only [BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,
      List.length_replicate,UnaryResources.copies_replicate]
  constructor
  · rw [costRange,hc]
    simp only [←List.replicate_one (a:=true),←List.replicate_add,BinaryEllipsoidInitial.indices_replicate]
  · rw [countRange,src_pack]
    simp only [BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,←List.replicate_one (a:=true),←List.replicate_add,BinaryEllipsoidInitial.indices_replicate]
lemma atInput_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) (p m : ℕ) :
    atInput (pairBits (pack δ D F S Δ g raw,pairBits (p.bits,m.bits)))=Fair.pack δ D F S Δ p m g raw := by
  simp only [atInput,atParams,source,price,count,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    src,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.natWords_bits,extra,Fair.raw,pack,Fair.pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
noncomputable def words (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) : List (List Bool) :=
  (List.ofFn (fun p:Fin (D.card*Δ+1)=>p)).flatMap (fun p=>List.ofFn (fun m:Fin (n+1)=>
    Repeat.FiniteTape.run Q d (Fair.pack δ D F S Δ p.val m.val g raw)))
lemma candidateWords_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    candidateWords Q d (pack δ D F S Δ g raw)=encode (words Q d δ D F S Δ g raw) := by
  rw [candidateWords,choices,(ranges_pack δ D F S Δ g raw hΔ).1,(ranges_pack δ D F S Δ g raw hΔ).2,
    cross_encode,mapWith_encode]
  simp only [flatMap_ofFn,List.map_flatten,List.map_ofFn,Function.comp_def,atChoice,
    atInput_pack,words]
lemma run_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    run Q d (pack δ D F S Δ g raw)=BinaryFinSet.encode
      (BinarySanitizedBest.output δ D F S S.card (words Q d δ D F S Δ g raw)) := by
  rw [run,Function.comp_apply,runInput,candidateWords_pack Q d δ D F S Δ g raw hΔ]
  have hs : sizeWord (pack δ D F S Δ g raw)=S.card.bits := by
    simp only [sizeWord,src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,
      Finset.length_sort,UnaryResources.lengthBits_eq,List.length_replicate]
  rw [hs]
  simp only [src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  exact BinarySanitizedBest.run_pack δ D F S S.card _
lemma word_mem (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) (p m : ℕ) (hp : p≤D.card*Δ) (hm : m≤n) :
    Repeat.FiniteTape.run Q d (Fair.pack δ D F S Δ p m g raw)∈words Q d δ D F S Δ g raw := by
  exact List.mem_flatMap.mpr ⟨⟨p,Nat.lt_succ_of_le hp⟩,List.mem_ofFn.mpr ⟨⟨p,Nat.lt_succ_of_le hp⟩,rfl⟩,
    List.mem_ofFn.mpr ⟨⟨m,Nat.lt_succ_of_le hm⟩,rfl⟩⟩
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
