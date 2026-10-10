import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.GlobalZero
import OAI.Combinatorics.KMedianRecovery.Encoding.MaskOutput

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable abbrev matrix := BinaryInputParser.Metric.matrix
noncomputable abbrev clients := BinaryNormalizeInput.P.clients
noncomputable abbrev facilities := BinaryNormalizeInput.P.facilities
noncomputable abbrev budget := BinaryInputParser.Metric.budget
end P
noncomputable def scales : List Bool→List Bool := BinaryInputParser.Stream.run ∘ BinaryInputParser.Metric.rawMatrix
noncomputable def scales_computes : PolyComputes scales :=
  BinaryInputParser.Metric.rawMatrix_computes.comp BinaryInputParser.Stream.run_computes
lemma scales_bits (I : RationalMetricInput) : scales I.bits=encode ((BinaryInputParser.Metric.flat I).map BinaryRational.encode) := by
  rw [scales,Function.comp_apply,BinaryInputParser.Metric.rawMatrix_bits,BinaryInputParser.Stream.run_code]
noncomputable def callInput (x : List Bool) : List Bool :=
  encode [extractPrefix (extractPrefix x),discardPrefix x,discardPrefix (extractPrefix x)]
noncomputable def callInput_computes : PolyComputes callInput := list_computes
  [extractPrefix ∘ extractPrefix,discardPrefix,discardPrefix ∘ extractPrefix] (by
    intro f hf;refine Classical.choice ?_;simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨extractPrefix_computes.comp extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩
    · exact ⟨extractPrefix_computes.comp discardPrefix_computes⟩)
lemma callInput_pack (I : RationalMetricInput) (raw : List Bool) (M : ℚ) :
    callInput (pairBits (pairBits (I.bits,raw),BinaryRational.encode M))=BinaryGlobalCall.pack I M raw := by
  simp only [callInput,extractPrefix_pairBits,discardPrefix_pairBits,BinaryGlobalCall.pack]
noncomputable def one (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool :=
  BinaryGlobalCall.run v C Q d ∘ callInput
noncomputable def one_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (one v C Q d) :=
  callInput_computes.comp (BinaryGlobalCall.run_computes v C Q d)
noncomputable def calls (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (one v C Q d) (pairBits (x,scales (extractPrefix x)))
noncomputable def calls_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (calls v C Q d) := by
  unfold calls
  simpa only [Function.comp_def,id_eq] using
    (id_computes.pair (extractPrefix_computes.comp scales_computes)).comp (mapWith_computes (one_computes v C Q d))
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := BinaryGlobalCall.demand Q ∘ callInput
noncomputable def demand_computes (Q : Polynomial ℕ) : PolyComputes (demand Q) := callInput_computes.comp (BinaryGlobalCall.demand_computes Q)
noncomputable def demands (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  mapWith (demand Q) (pairBits (pairBits (x,[]),scales x))
noncomputable def demands_computes (Q : Polynomial ℕ) : PolyComputes (demands Q) := by
  unfold demands
  simpa only [Function.comp_def,id_eq] using
    ((id_computes.pair (const_computes [])).pair scales_computes).comp (mapWith_computes (demand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demands_computes Q).lengthPolynomial
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [P.facilities x,[],(1:ℕ).bits]
noncomputable def fallbackInput_computes : PolyComputes fallbackInput :=
  cons_computes BinaryNormalizeInput.P.facilities_computes
    (cons_computes (const_computes []) (cons_computes (const_computes (1:ℕ).bits) (const_computes [])))
noncomputable def fallback : List Bool→List Bool := BinaryCompletionPad.run ∘ fallbackInput
noncomputable def fallback_computes : PolyComputes fallback := fallbackInput_computes.comp BinaryCompletionPad.run_computes
noncomputable def zeroInput (x : List Bool) : List Bool := encode [P.matrix x,P.clients x,P.facilities x]
noncomputable def zeroInput_computes : PolyComputes zeroInput := cons_computes BinaryInputParser.Metric.matrix_computes
  (cons_computes BinaryNormalizeInput.P.clients_computes (cons_computes BinaryNormalizeInput.P.facilities_computes (const_computes [])))
noncomputable def zero : List Bool→List Bool := BinaryGlobalZero.run ∘ zeroInput
noncomputable def zero_computes : PolyComputes zero := zeroInput_computes.comp BinaryGlobalZero.run_computes
noncomputable def candidates (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  cons (zero (extractPrefix x)) (calls v C Q d x)
noncomputable def candidates_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidates v C Q d) := by
  unfold candidates
  simpa only [Function.comp_def] using
    cons_computes (extractPrefix_computes.comp zero_computes) (calls_computes v C Q d)
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback candidates
noncomputable def selectInput (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [P.matrix (extractPrefix x),P.clients (extractPrefix x),P.facilities (extractPrefix x),
    fallback (extractPrefix x),P.budget (extractPrefix x),candidates v C Q d x]
noncomputable def selectInput_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (selectInput v C Q d) :=
  cons_computes (extractPrefix_computes.comp BinaryInputParser.Metric.matrix_computes)
    (cons_computes (extractPrefix_computes.comp BinaryNormalizeInput.P.clients_computes)
      (cons_computes (extractPrefix_computes.comp BinaryNormalizeInput.P.facilities_computes)
        (cons_computes (extractPrefix_computes.comp fallback_computes)
          (cons_computes (extractPrefix_computes.comp BinaryInputParser.Metric.budget_computes)
            (cons_computes (candidates_computes v C Q d) (const_computes []))))))
noncomputable def select (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool :=
  BinarySanitizedBest.run ∘ selectInput v C Q d
noncomputable def select_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (select v C Q d) :=
  (selectInput_computes v C Q d).comp BinarySanitizedBest.run_computes
noncomputable def maskCount : List Bool→List Bool := RawUnary.run ∘ BinaryInputParser.Metric.clients ∘ extractPrefix
noncomputable def maskCount_computes : PolyComputes maskCount :=
  (extractPrefix_computes.comp BinaryInputParser.Metric.clients_computes).comp RawUnary.run_computes
noncomputable def run (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  BinaryMaskOutput.run (pairBits (maskCount x,select v C Q d x))
noncomputable def run_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run v C Q d) :=
  (maskCount_computes.pair (select_computes v C Q d)).comp BinaryMaskOutput.run_computes
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryGlobalCall.run BinaryGlobalCall.demand budget select BinarySanitizedBest.output
noncomputable def start (I : RationalMetricInput) : Finset (Fin I.pointCount) := Canonical.pad I.facilities ∅ 1
lemma start_subset (I : RationalMetricInput) : start I⊆I.facilities := Canonical.pad_subset _ _ _ (Finset.empty_subset _)
lemma start_card (I : RationalMetricInput) : (start I).card=1 :=
  Canonical.pad_card _ _ _ (Finset.empty_subset _) (by simp) I.facilities_nonempty.card_pos
lemma start_nonempty (I : RationalMetricInput) : (start I).Nonempty := Finset.card_pos.mp (by rw [start_card];norm_num)
lemma start_budget (I : RationalMetricInput) : (start I).card≤I.budget := by rw [start_card];exact I.budget_pos
lemma fallback_bits (I : RationalMetricInput) : fallback I.bits=BinaryFinSet.encode (start I) := by
  rw [fallback,Function.comp_apply,fallbackInput,P.facilities,BinaryNormalizeInput.P.facilities_bits]
  have he : BinaryFinSet.encode (∅:Finset (Fin I.pointCount))=[] := by simp only [BinaryFinSet.encode_eq,Finset.sort_empty,List.map_nil,encode]
  simpa only [he,start] using BinaryFinSet.pad_pack I.facilities ∅ 1
lemma zero_bits (I : RationalMetricInput) : zero I.bits=BinaryFinSet.encode
    (BinaryGlobalZero.output I.distance I.clients I.facilities I.facilities_nonempty) := by
  rw [zero,Function.comp_apply,zeroInput,P.matrix,P.clients,P.facilities,BinaryInputParser.Metric.matrix_bits,
    BinaryNormalizeInput.P.clients_bits,BinaryNormalizeInput.P.facilities_bits]
  have hh:=BinaryGlobalZero.run_pack I.distance I.clients I.facilities I.facilities_nonempty
  simpa only [BinaryGlobalZero.pack,BinaryMetricArrays.pack,BinaryFinSet.table_enum,Rectangular.encode,RationalMatrix.encode] using hh
noncomputable def words (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) : List (List Bool) :=
  zero I.bits::(BinaryInputParser.Metric.flat I).map (fun M=>BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M raw))
lemma calls_bits (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) :
    calls v C Q d (pairBits (I.bits,raw))=encode ((BinaryInputParser.Metric.flat I).map
      (fun M=>BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M raw))) := by
  rw [calls,extractPrefix_pairBits,scales_bits,mapWith_encode,List.map_map]
  simp only [one,Function.comp_def,callInput_pack]
lemma candidates_bits (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) :
    candidates v C Q d (pairBits (I.bits,raw))=encode (words v C Q d I raw) := by
  rw [candidates,extractPrefix_pairBits,calls_bits];rfl
noncomputable def output (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) : Finset (Fin I.pointCount) :=
  BinarySanitizedBest.output I.distance I.clients I.facilities (start I) I.budget (words v C Q d I raw)
lemma select_bits (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) :
    select v C Q d (pairBits (I.bits,raw))=BinaryFinSet.encode (output v C Q d I raw) := by
  rw [select,Function.comp_apply,selectInput,candidates_bits]
  simp only [extractPrefix_pairBits,BinaryInputParser.Metric.matrix_bits,BinaryNormalizeInput.P.clients_bits,
    BinaryNormalizeInput.P.facilities_bits,fallback_bits,BinaryInputParser.Metric.budget_bits]
  exact BinarySanitizedBest.run_pack _ _ _ _ _ _
lemma run_bits (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) :
    run v C Q d (pairBits (I.bits,raw))=I.outputBits (output v C Q d I raw) := by
  rw [run,select_bits,maskCount,Function.comp_apply,Function.comp_apply,extractPrefix_pairBits,
    BinaryInputParser.Metric.clients_bits]
  simp only [RawUnary.run,BinaryInputParser.Metric.mask,List.length_ofFn]
  exact BinaryMaskOutput.run_set _
lemma output_feasible (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) :
    output v C Q d I raw⊆I.facilities ∧ (output v C Q d I raw).Nonempty ∧ (output v C Q d I raw).card≤I.budget :=
  BinarySanitizedBest.output_feasible _ _ _ _ _ _ (start_subset I) (start_nonempty I) (start_budget I)
lemma flat_mem (I : RationalMetricInput) (i j : Fin I.pointCount) : I.distance i j∈BinaryInputParser.Metric.flat I :=
  List.mem_flatten.mpr ⟨List.ofFn (I.distance i),List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩
lemma demand_bound (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (hM : M∈BinaryInputParser.Metric.flat I) :
    (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length≤(budget Q).eval I.bits.length := by
  have hm : demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode M))∈
      (BinaryInputParser.Metric.flat I).map (fun r=>demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode r))) :=
    List.mem_map.mpr ⟨M,hM,rfl⟩
  have hb:=length_member_le_encode hm
  have hl : (demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode M))).length=
      (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length := by
    rw [demand,Function.comp_apply,callInput_pack,BinaryGlobalCall.demand_length]
  rw [hl] at hb
  have he : demands Q I.bits=encode ((BinaryInputParser.Metric.flat I).map
      (fun r=>demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode r)))) := by
    rw [demands,scales_bits,mapWith_encode,List.map_map];rfl
  rw [←he] at hb
  exact hb.trans (by simpa only [budget] using (demands_computes Q).length_bound I.bits)
lemma realCost_eq (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) :
    @Completion.realCost _ I.metric I.clients S=(I.cost S:ℝ) := by
  have hh : @Completion.realCost _ I.metric I.clients S=@cost _ I.metric I.clients S := by
    by_cases hS:S.Nonempty
    · simp only [Completion.realCost,cost,connection,dite_eq_left hS,Completion.distanceTo]
    · simp only [Completion.realCost,cost,connection,dite_eq_right hS,Finset.sum_const_zero]
  exact hh.trans (I.metric_cost S)
lemma cost_le_word (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool)
    (U : Finset (Fin I.pointCount)) (hUF : U⊆I.facilities) (hU : U.Nonempty) (hUk : U.card≤I.budget)
    (hmem : BinaryFinSet.encode U∈words v C Q d I raw) :
    (I.cost (output v C Q d I raw):ℝ)≤(I.cost U:ℝ) := by
  have hh:=@BinarySanitizedBest.realCost_le_good _ I.metric I.distance (fun _ _=>rfl) I.clients I.facilities
    (start I) I.budget (words v C Q d I raw) (start_subset I) (start_nonempty I) (start_budget I) U hUF hU hUk hmem
  simpa only [realCost_eq,output] using hh
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
