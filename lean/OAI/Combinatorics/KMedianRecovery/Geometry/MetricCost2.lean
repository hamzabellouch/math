import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalBest
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionFairCorrect

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordOperations WordList
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode S]
def connection (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (x : Fin n) : ℚ :=
  RationalMin.minimum (List.ofFn (fun j:Fin S.card=>δ x (SortedIndex.enum S j)))
def cost (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) : ℚ :=
  ∑ i:Fin D.card,connection δ S (SortedIndex.enum D i)
noncomputable def near (x : List Bool) : List Bool := RationalMin.run (discardPrefix x)
noncomputable def near_computes : PolyComputes near := discardPrefix_computes.comp RationalMin.run_computes
noncomputable def run (x : List Bool) : List Bool := RationalArray.sumWords
  (mapWith near (pairBits ([],BinaryMetricArrays.run x)))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := ((const_computes []).pair BinaryMetricArrays.run_computes).comp
    ((mapWith_computes near_computes).comp RationalArray.sumWords_computes)
  simpa only [Function.comp_def] using computes
lemma run_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) :
    run (pack δ D S)=BinaryRational.encode (cost δ D S) := by
  have hp : pack δ D S=BinaryMetricArrays.pack δ (SortedIndex.enum D) (SortedIndex.enum S) := by
    simp only [pack,BinaryMetricArrays.pack,BinaryFinSet.table_enum]
  rw [run,hp,BinaryMetricArrays.run_pack,mapWith_ofFn]
  simp only [near,discardPrefix_pairBits,RationalMatrix.rowEncode_eq]
  simp only [show ∀i:Fin D.card,RationalMin.run (encode (List.ofFn
      (fun j:Fin S.card=>BinaryRational.encode (δ (SortedIndex.enum D i) (SortedIndex.enum S j)))))=
      BinaryRational.encode (connection δ S (SortedIndex.enum D i)) from fun i=>by
    simpa only [RationalArray.encode,List.map_ofFn,Function.comp_def,connection] using
      RationalMin.run_encode (List.ofFn (fun j:Fin S.card=>δ (SortedIndex.enum D i) (SortedIndex.enum S j)))]
  simpa only [RationalArray.encode,List.map_ofFn,Function.comp_def,List.sum_ofFn,cost] using
    RationalArray.sumWords_encode (List.ofFn (fun i:Fin D.card=>connection δ S (SortedIndex.enum D i)))
variable [PseudoMetricSpace (Fin n)]
lemma connection_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (S : Finset (Fin n)) (hS : S.Nonempty) (x : Fin n) :
    (connection δ S x:ℝ)=Completion.distanceTo S hS x := by
  have he : List.ofFn (fun j:Fin S.card=>δ x (SortedIndex.enum S j))=(S.sort (·≤·)).map (δ x) :=
    (SortedIndex.map_enum S (δ x)).symm
  have hne : (S.sort (·≤·)).map (δ x)≠[] := by
    intro hem
    have hl:=congrArg List.length hem
    simp only [List.length_map,Finset.length_sort,List.length_nil] at hl
    exact hS.card_pos.ne' hl
  rw [connection,he]
  apply le_antisymm
  · apply Finset.le_inf'
    intro y hy
    rw [←hδ x y]
    exact_mod_cast RationalMin.minimum_le_mem ((S.sort (·≤·)).map (δ x)) (δ x y)
      (List.mem_map.mpr ⟨y,(Finset.mem_sort (·≤·)).mpr hy,rfl⟩)
  · obtain ⟨y,hy,hmin⟩:=Finset.exists_min_image S (δ x) hS
    have hh : δ x y≤RationalMin.minimum ((S.sort (·≤·)).map (δ x)) := by
      apply RationalMin.minimum_lower _ _ hne
      intro q hq
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
      exact hmin z ((Finset.mem_sort (·≤·)).mp hz)
    exact (Completion.distanceTo_le hS x hy).trans (hδ x y ▸ Rat.cast_le.mpr hh)
lemma cost_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) :
    (cost δ D S:ℝ)=Completion.realCost D S := by
  simp only [cost,Rat.cast_sum,connection_cast δ hδ S hS,Completion.realCost,dite_eq_left hS]
  exact SortedIndex.sum_enum D (Completion.distanceTo S hS)
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def score (x : List Bool) : List Bool := BinaryRational.negWords (BinaryMetricCost.run
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),discardPrefix x]))
noncomputable def score_computes : PolyComputes score :=
  (cons_computes (extractPrefix_computes.comp (field_computes 0))
    (cons_computes (extractPrefix_computes.comp (field_computes 1))
      (cons_computes discardPrefix_computes (const_computes [])))).comp
        (BinaryMetricCost.run_computes.comp BinaryRational.negWords_computes)
def context (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D]
lemma score_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) :
    score (pairBits (context δ D,BinaryFinSet.encode S))=BinaryRational.encode (-BinaryMetricCost.cost δ D S) := by
  simp only [score,context,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [←BinaryMetricCost.pack,BinaryMetricCost.run_pack]
  exact BinaryRational.negWords_encode _
def best (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) : Finset (Fin n) :=
  OrderedMaximum.run (fun U=> -BinaryMetricCost.cost δ D U) S xs
noncomputable def run (x : List Bool) : List Bool := BinaryRationalBest.run score x
noncomputable def run_computes : PolyComputes run := BinaryRationalBest.run_computes score_computes
lemma run_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    run (BinaryRationalBest.pack (context δ D) (BinaryFinSet.encode S) (xs.map BinaryFinSet.encode))=
      BinaryFinSet.encode (best δ D S xs) :=
  BinaryRationalBest.run_pack BinaryFinSet.encode score (context δ D) _ (score_pack δ D) S xs
lemma best_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    best δ D S xs=S ∨ best δ D S xs∈xs := OrderedMaximum.mem _ _ _
lemma cost_le_self (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    BinaryMetricCost.cost δ D (best δ D S xs)≤BinaryMetricCost.cost δ D S := by
  exact neg_le_neg_iff.mp (OrderedMaximum.own_le (fun U=> -BinaryMetricCost.cost δ D U) S xs)
lemma cost_le_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (U : Finset (Fin n)) (hU : U∈xs) :
    BinaryMetricCost.cost δ D (best δ D S xs)≤BinaryMetricCost.cost δ D U := by
  exact neg_le_neg_iff.mp (OrderedMaximum.score_le (fun U=> -BinaryMetricCost.cost δ D U) S xs U hU)
lemma best_property (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (P : Finset (Fin n)→Prop) (hS : P S) (hxs : ∀ U∈xs,P U) : P (best δ D S xs) := by
  rcases best_mem δ D S xs with h|h
  · rwa [h]
  · exact hxs _ h
variable [PseudoMetricSpace (Fin n)]
lemma realCost_le_mem (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (xs : List (Finset (Fin n)))
    (hxs : ∀ U∈xs,U.Nonempty) (U : Finset (Fin n)) (hU : U∈xs) :
    Completion.realCost D (best δ D S xs)≤Completion.realCost D U := by
  rw [←BinaryMetricCost.cost_cast δ hδ D U (hxs U hU),
    ←BinaryMetricCost.cost_cast δ hδ D (best δ D S xs) (best_property δ D S xs Finset.Nonempty hS hxs)]
  exact_mod_cast cost_le_mem δ D S xs U hU
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
