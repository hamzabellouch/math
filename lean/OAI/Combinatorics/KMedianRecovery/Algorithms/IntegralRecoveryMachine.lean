import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.RecoveryOptionMachine
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerTraceMachine
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerParameters

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def params : List Bool→List Bool := extractPrefix
noncomputable def sampleRaw : List Bool→List Bool := extractPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def completeRaw : List Bool→List Bool := discardPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def extra : List Bool→List Bool := extractPrefix ∘ discardPrefix
noncomputable def sampleRaw_computes : PolyComputes sampleRaw := discardPrefix_computes.comp (discardPrefix_computes.comp extractPrefix_computes)
noncomputable def completeRaw_computes : PolyComputes completeRaw := discardPrefix_computes.comp (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def extra_computes : PolyComputes extra := discardPrefix_computes.comp extractPrefix_computes
noncomputable def mword : List Bool→List Bool := BinarySampler.Parameters.unary 7 ∘ params
noncomputable def mword_computes : PolyComputes mword := extractPrefix_computes.comp (BinarySampler.Parameters.unary_computes 7)
noncomputable def cfg : List Bool→List Bool := BinarySampler.Parameters.run ∘ params
noncomputable def cfg_computes : PolyComputes cfg := extractPrefix_computes.comp BinarySampler.Parameters.run_computes
noncomputable def precision : List Bool→List Bool := BinarySampler.Parameters.precision ∘ params
noncomputable def precision_computes : PolyComputes precision := extractPrefix_computes.comp BinarySampler.Parameters.precision_computes
noncomputable def sampleContext (x : List Bool) : List Bool :=
  encode [cfg x,mword x,mword x++mword x,precision x,sampleRaw x]
noncomputable def sampleContext_computes : PolyComputes sampleContext := cons_computes cfg_computes
  (cons_computes mword_computes (cons_computes (mword_computes.append mword_computes)
    (cons_computes precision_computes (cons_computes sampleRaw_computes (const_computes [])))))
noncomputable def recoveryContext (x : List Bool) : List Bool :=
  encode [src 0 x,src 2 x,src 3 x,src 4 x,BinaryRational.natWords (src 5 x),pairBits ([],[]),src 1 x,mword x,extra x,completeRaw x]
attribute [local irreducible] src mword extra completeRaw BinaryRational.natWords
noncomputable def recoveryContext_computes : PolyComputes recoveryContext := list_computes
  [src 0,src 2,src 3,src 4,BinaryRational.natWords ∘ src 5,fun _=>pairBits ([],[]),src 1,mword,extra,completeRaw] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨(src_computes 5).comp BinaryRational.natWords_computes⟩ |
      exact ⟨const_computes _⟩ | exact ⟨mword_computes⟩ | exact ⟨extra_computes⟩ | exact ⟨completeRaw_computes⟩)
noncomputable def candidateWords (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (BinaryRecovery.atOption d) (pairBits (recoveryContext x,BinarySampler.Trace.run (sampleContext x)))
attribute [local irreducible] mapWith recoveryContext sampleContext BinarySampler.Trace.run
noncomputable def candidateWords_computes (d : ℕ) : PolyComputes (candidateWords d) :=
  PolyComputes.comp
    (f := fun input=>pairBits (recoveryContext input,BinarySampler.Trace.run (sampleContext input)))
    (g := mapWith (BinaryRecovery.atOption d))
    (recoveryContext_computes.pair (PolyComputes.comp (f := sampleContext) (g := BinarySampler.Trace.run)
      sampleContext_computes BinarySampler.Trace.run_computes))
    (mapWith_computes (BinaryRecovery.atOption_computes d))
noncomputable def metricContext (x : List Bool) : List Bool := encode [src 0 x,src 2 x]
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (src_computes 0) (cons_computes (src_computes 2) (const_computes []))
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  BinaryMetricBest.run (pairBits (metricContext x,pairBits (src 4 x,candidateWords d x)))
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  (metricContext_computes.pair ((src_computes 4).pair (candidateWords_computes d))).comp BinaryMetricBest.run_computes
def pack {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (extra : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool) : List Bool :=
  pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,
    pairBits (extra,pairBits (BinarySeed.raw (ds:=[2*m]) seed,complete)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] params cfg mword precision sampleRaw completeRaw extra src
  BinarySampler.Parameters.run BinarySampler.Parameters.precision BinarySampler.Parameters.unary
variable {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
  (g : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool)
lemma params_pack : params (pack δ D F S Δ P m g seed complete)=BinarySampler.Parameters.pack δ D F S Δ P m := by
  simp only [params,pack,extractPrefix_pairBits]
lemma data_pack : extra (pack δ D F S Δ P m g seed complete)=g ∧
    sampleRaw (pack δ D F S Δ P m g seed complete)=BinarySeed.raw (ds:=[2*m]) seed ∧
    completeRaw (pack δ D F S Δ P m g seed complete)=complete := by
  simp only [extra,sampleRaw,completeRaw,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,and_self]
lemma src_pack (j : ℕ) : src j (pack δ D F S Δ P m g seed complete)=
    field j (BinarySampler.Parameters.pack δ D F S Δ P m) := by
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits]
lemma mword_pack (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    mword (pack δ D F S Δ P m g seed complete)=List.replicate m true := by
  rw [mword,Function.comp_apply,params_pack]
  exact (BinarySampler.Parameters.unary_pack δ D F S Δ P m hm hΔ).1
lemma cfg_pack (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    cfg (pack δ D F S Δ P m g seed complete)=BinarySampler.config δ D F S Δ P (1/1000000) m
      BinarySampler.Parameters.M BinarySampler.Parameters.E (RadiusMenus.thirdSize mainKappa m) := by
  rw [cfg,Function.comp_apply,params_pack]
  exact BinarySampler.Parameters.run_pack δ D F S Δ P m hm hΔ
lemma precision_pack (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    precision (pack δ D F S Δ P m g seed complete)=List.replicate (integralPrecision D (Δ:ℝ) m) true := by
  rw [precision,Function.comp_apply,params_pack]
  exact BinarySampler.Parameters.precision_pack δ D F S Δ P m hm hΔ
lemma sampleContext_pack (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    sampleContext (pack δ D F S Δ P m g seed complete)=
      BinarySampler.Trace.pack (BinarySampler.config δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M
        BinarySampler.Parameters.E (RadiusMenus.thirdSize mainKappa m)) m seed := by
  rw [sampleContext,cfg_pack δ D F S Δ P m g seed complete hm hΔ,
    mword_pack δ D F S Δ P m g seed complete hm hΔ,precision_pack δ D F S Δ P m g seed complete hm hΔ,
    (data_pack δ D F S Δ P m g seed complete).2.1]
  simp only [BinarySampler.Trace.pack,←List.replicate_add,two_mul]
lemma recoveryContext_pack (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    recoveryContext (pack δ D F S Δ P m g seed complete)=
      BinaryRecovery.pack δ D F S Δ RationalSampling.State.initial m g complete := by
  rw [recoveryContext,mword_pack δ D F S Δ P m g seed complete hm hΔ,
    (data_pack δ D F S Δ P m g seed complete).1,(data_pack δ D F S Δ P m g seed complete).2.2]
  simp only [src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryRational.natWords_bits,BinaryRecovery.pack]
  congr 1
  simp only [BinarySamplingState.encode,RationalSampling.State.initial,BinaryFinSet.encode_eq,
    Finset.sort_empty,List.map_nil,BinaryNearestLeaf.leavesBits,WordList.encode]
lemma metricContext_pack : metricContext (pack δ D F S Δ P m g seed complete)=BinaryMetricBest.context δ D := by
  simp only [metricContext,src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryMetricBest.context]
lemma start_pack : src 4 (pack δ D F S Δ P m g seed complete)=BinaryFinSet.encode S := by
  simp only [src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
