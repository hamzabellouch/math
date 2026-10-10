import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricAnchor
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoverySelection

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output Repeat.output budget Fair.pack

lemma integral_recovery (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (N : ℕ) (g : List Bool) (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (budget Q).eval (pack δQ D F S Δ g []).length
    (∀ seed:Fin K→Bool,run Q d (pack δQ D F S Δ g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δQ D F S Δ g (List.ofFn seed))) ∧
    (∀ seed:Fin K→Bool,output Q d δQ D F S Δ g (List.ofFn seed)⊆F ∧
      (output Q d δQ D F S Δ g (List.ofFn seed)).Nonempty ∧
      (output Q d δQ D F S Δ g (List.ofFn seed)).card≤S.card ∧
      realCost D (output Q d δQ D F S Δ g (List.ofFn seed))≤realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨Q,d,hd⟩:=polynomial_recovery A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound hsep N g hN hlog
  dsimp only
  have hδQ : ∀ i j,((δ i j:ℚ):ℝ)=dist i j := by simpa only [Rat.cast_natCast] using hδ
  have hboundQ : ∀ x,∀ f∈F,(δ x f:ℚ)≤Δ := by intro x f hf; exact_mod_cast hbound x f hf
  have hP := C.comparison_cost_positive hD F hOF hsep
  by_cases hz : C.bad.card=0
  · have hfall := C.no_bad_proxy_cost hS hz
    have hs (raw : List Bool) : realCost D (output Q d (fun i j=>(δ i j:ℚ)) D F S Δ g raw)≤
        (197/100:ℝ)*comparisonCost D C.assign := by
      have hh:=cost_le_start Q d (fun i j=>(δ i j:ℚ)) hδQ D F S hSF hS Δ g raw
      linarith
    refine ⟨fun _=>run_output Q d _ D F S Δ g _ hcap,?_,?_,?_⟩
    · intro seed
      have hf:=output_feasible Q d (fun i j=>(δ i j:ℚ)) D F S hSF hS Δ g (List.ofFn seed)
      exact ⟨hf.1,hf.2.1,hf.2.2,cost_le_start Q d _ hδQ D F S hSF hS Δ g _⟩
    · have he : probability (fun seed:Fin ((budget Q).eval (pack (fun i j=>(δ i j:ℚ)) D F S Δ g []).length)→Bool=>
          realCost D (output Q d (fun i j=>(δ i j:ℚ)) D F S Δ g (List.ofFn seed))≤
            (197/100:ℝ)*comparisonCost D C.assign)=1 := by
        have hh : (fun seed:Fin ((budget Q).eval (pack (fun i j=>(δ i j:ℚ)) D F S Δ g []).length)→Bool=>
          realCost D (output Q d (fun i j=>(δ i j:ℚ)) D F S Δ g (List.ofFn seed))≤
            (197/100:ℝ)*comparisonCost D C.assign)=(fun _=>True) := by
          funext seed; exact propext ⟨fun _=>trivial,fun _=>hs _⟩
        rw [hh]; simp [probability]
      rw [he]
      have hh:=FailureBudget.failure_pos IntegralAssembly.gamma_pos e N
      linarith
    · have hbase : (0:ℝ)≤realCost D S := by
        rw [realCost,dite_eq_left hS]
        exact Finset.sum_nonneg (fun _ _=>distanceTo_nonneg _ _ _)
      have hmean:=average_mono (fun seed:Fin ((budget Q).eval (pack (fun i j=>(δ i j:ℚ)) D F S Δ g []).length)→Bool=>hs (List.ofFn seed))
      rw [average_const] at hmean
      exact hmean.trans (le_add_of_nonneg_right (mul_nonneg hbase (FailureBudget.failure_pos IntegralAssembly.gamma_pos e N).le))
  · obtain ⟨p,hp,heq⟩:=C.integer_comparison_cost F hOF δ Δ (fun w _ f _=>hδ w f) (fun w _ f hf=>hbound w f hf)
    obtain ⟨r0,hr0⟩:=hS
    exact hd (fun i j=>(δ i j:ℚ)) hδQ D F S O C hD hSF hOF ⟨r0,hr0⟩ Δ hΔ hcap hboundQ p hp heq.symm
      hsep hP (Nat.pos_of_ne_zero hz) (by simpa only [Fintype.card_fin] using C.bad.card_le_univ) r0 r0 N g hN hlog
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace R
noncomputable abbrev run := BinaryIntegralRecovery.Guesses.run
noncomputable abbrev budget := BinaryIntegralRecovery.Guesses.budget
abbrev pack := @BinaryIntegralRecovery.Guesses.pack
end R
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,Δ.bits,k.bits,g,raw]
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def anchorInput (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,discardPrefix x]
noncomputable def anchorInput_computes : PolyComputes anchorInput := list_computes
  [src 0,src 1,src 2,src 3,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨discardPrefix_computes⟩)
noncomputable def anchor : List Bool→List Bool := BinaryMetricAnchor.run ∘ anchorInput
noncomputable def anchor_computes : PolyComputes anchor := anchorInput_computes.comp BinaryMetricAnchor.run_computes
noncomputable def recoveryParams (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,anchor x,src 4 x,BinaryRational.encode 0,(0:ℕ).bits]
noncomputable def recoveryParams_computes : PolyComputes recoveryParams := list_computes
  [src 0,src 1,src 2,src 3,anchor,src 4,fun _=>BinaryRational.encode 0,fun _=>(0:ℕ).bits] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨anchor_computes⟩ | exact ⟨const_computes _⟩)
noncomputable def bare (x : List Bool) : List Bool := pairBits (recoveryParams x,pairBits (src 6 x,[]))
noncomputable def bare_computes : PolyComputes bare := recoveryParams_computes.pair ((src_computes 6).pair (const_computes []))
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter (R.budget Q) := PolynomialCounter.choose _
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := (counter Q).word ∘ bare
noncomputable def demand_computes (Q : Polynomial ℕ) : PolyComputes (demand Q) := bare_computes.comp (counter Q).computes
attribute [local irreducible] counter demand bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.run
noncomputable def cutRaw (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RawTake.run (pairBits (UnaryResources.lengthBits (demand Q x),src 7 x))
noncomputable def cutRaw_computes (Q : Polynomial ℕ) : PolyComputes (cutRaw Q) :=
  (((demand_computes Q).comp UnaryResources.lengthBits_computes).pair (src_computes 7)).comp RawTake.run_computes
noncomputable def callInput (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairBits (recoveryParams x,pairBits (src 6 x,cutRaw Q x))
noncomputable def callInput_computes (Q : Polynomial ℕ) : PolyComputes (callInput Q) :=
  recoveryParams_computes.pair ((src_computes 6).pair (cutRaw_computes Q))
noncomputable def call (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := R.run Q d ∘ callInput Q
noncomputable def call_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (call Q d) :=
  (callInput_computes Q).comp (BinaryIntegralRecovery.Guesses.run_computes Q d)
noncomputable def ranks (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (Count.run (field 3 x)++[true])
noncomputable def ranks_computes : PolyComputes ranks :=
  (((field_computes 3).comp Count.run_computes).append (const_computes [true])).comp BinaryEllipsoidInitial.indices_computes
noncomputable def calls (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool := mapWith (call Q d) (pairBits (x,ranks x))
attribute [local irreducible] mapWith
noncomputable def calls_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (calls Q d) :=
  PolyComputes.comp (f := fun input=>pairBits (input,ranks input)) (g := mapWith (call Q d))
    (id_computes.pair ranks_computes) (mapWith_computes (call_computes Q d))
noncomputable def start (x : List Bool) : List Bool := anchor (pairBits (x,field 5 x))
noncomputable def start_computes : PolyComputes start := (id_computes.pair (field_computes 5)).comp anchor_computes
noncomputable def runInput (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 2 x,field 3 x,start x,field 5 x,calls Q d x]
attribute [local irreducible] start calls
noncomputable def runInput_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (runInput Q d) := list_computes
  [field 0,field 2,field 3,start,field 5,calls Q d] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨start_computes⟩ | exact ⟨calls_computes Q d⟩)
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := BinarySanitizedBest.run ∘ runInput Q d
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (runInput_computes Q d).comp BinarySanitizedBest.run_computes
noncomputable def demands (Q : Polynomial ℕ) (x : List Bool) : List Bool := mapWith (demand Q) (pairBits (x,ranks x))
noncomputable def demands_computes (Q : Polynomial ℕ) : PolyComputes (demands Q) :=
  PolyComputes.comp (f := fun input=>pairBits (input,ranks input)) (g := mapWith (demand Q))
    (id_computes.pair ranks_computes) (mapWith_computes (demand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demands_computes Q).lengthPolynomial
lemma anchorInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ) :
    anchorInput (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryMetricAnchor.pack δ D F r := by
  simp only [anchorInput,pack,src,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryMetricAnchor.pack]
lemma anchor_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ) :
    anchor (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r) := by
  rw [anchor,Function.comp_apply,anchorInput_pack]
lemma ranks_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) :
    ranks (pack δ D F Δ k g raw)=encode (List.ofFn (fun r:Fin (F.card+1)=>r.val.bits)) := by
  simp only [ranks,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,
    ←List.replicate_one (a:=true),←List.replicate_add,BinaryEllipsoidInitial.indices_replicate]
noncomputable def words (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List (List Bool) :=
  List.ofFn (fun r:Fin (F.card+1)=>call Q d (pairBits (pack δ D F Δ k g raw,r.val.bits)))
lemma calls_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) :
    calls Q d (pack δ D F Δ k g raw)=encode (words Q d δ D F Δ k g raw) := by
  rw [calls,ranks_pack,mapWith_ofFn]
  rfl
lemma start_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) :
    start (pack δ D F Δ k g raw)=BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k) := by
  rw [start]
  have he : field 5 (pack δ D F Δ k g raw)=k.bits := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [he,anchor_pack]
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
