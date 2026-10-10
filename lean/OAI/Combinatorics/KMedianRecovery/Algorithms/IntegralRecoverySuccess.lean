import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryFeasible
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoverySuccess
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerPrefixSuccess

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open Completion FiniteSampling Sampling Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_success
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hΔ : 1≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0<comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) :
    ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*
      ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))≤
      probability (fun seed:(Fin (2*C.bad.card)→Fin (integralPrecision D (Δ:ℝ) C.bad.card)→Bool)×
          (Fin (BinaryRecovery.tapeSize (n+1))→Bool)=>realCost D
        (result δ D F S Δ P C.bad.card hm r0 y0 seed.1 seed.2)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  let E:=fun sample:Fin (2*C.bad.card)→Fin (integralPrecision D (Δ:ℝ) C.bad.card)→Bool=>
    ∃ i:Fin (2*C.bad.card+1),C.stop hD (Δ:ℝ) ((stateAt δ D F S Δ P C.bad.card sample i).map RationalSampling.State.real)
  have hsample : (1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card≤probability E := by
    have hh := RationalSampling.prefix_success δ hδ D S O C hD F hOF hSF (Δ:ℚ) P
      (by exact_mod_cast hΔ) hPeq hsep hP hm0
    have hcast : ((Δ:ℚ):ℝ)=(Δ:ℝ) := by simp only [Rat.cast_natCast]
    generalize he : ((Δ:ℚ):ℝ)=dr at hh
    rw [show dr=(Δ:ℝ) from he.symm.trans hcast] at hh
    simpa only [E,stateAt,BinarySampler.Parameters.M,BinarySampler.Parameters.E] using hh
  apply (mul_le_mul_of_nonneg_right hsample (by positivity : 0≤(1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))).trans
  refine probability_prod_lower E (fun sample complete=>realCost D
    (result δ D F S Δ P C.bad.card hm r0 y0 sample complete)≤(197/100:ℝ)*comparisonCost D C.assign) ?_
  intro sample hsamp
  obtain ⟨i,hi⟩:=hsamp
  cases hst : stateAt δ D F S Δ P C.bad.card sample i with
  | none=>simp only [hst,Option.map_none,stop] at hi
  | some s=>
    rw [hst,Option.map_some] at hi
    change C.Correct hD (1/1000000) s.real ∧
      C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign ∧
      C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign at hi
    have hp : s.leaves.length≤n+1 := ((stateAt_bounded δ D F S Δ P C.bad.card sample i s hst).1.trans hm).trans (Nat.le_succ n)
    have hgood := BinaryRecovery.result_success δ hδ D F S O C hD hSF hOF hS (Δ:ℚ)
      (by positivity) hbound s hi.1 hP hm0 (by simpa only [Rat.cast_natCast] using hi.2.2)
      (by simpa only [Rat.cast_natCast] using hi.2.1) (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0
    apply hgood.trans
    apply probability_mono
    intro complete hc
    have hl:=result_cost_le_prefix δ hδ D F S hSF hS Δ hbound P C.bad.card hm r0 y0 sample complete i
    rw [hst,optionOutput_some δ D F S Δ C.bad.card hm r0 y0 complete s hp] at hl
    exact hl.trans hc
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
noncomputable def sampleCount (x : List Bool) : List Bool :=
  (2*(mword x).length*(precision x).length).bits
noncomputable def sampleCount_computes : PolyComputes sampleCount := by
  have hh := NatOps.mul (NatOps.mul (const_computes (2:ℕ).bits)
    (mword_computes.comp UnaryResources.lengthBits_computes))
    (precision_computes.comp UnaryResources.lengthBits_computes)
  change PolyComputes (fun x=>(2*(mword x).length*(precision x).length).bits)
  simpa only [UnaryResources.lengthBits_eq,value_bits,Function.comp_def] using hh
noncomputable def raw : List Bool→List Bool := discardPrefix ∘ discardPrefix
noncomputable def raw_computes : PolyComputes raw := discardPrefix_computes.comp discardPrefix_computes
noncomputable def repack (x : List Bool) : List Bool := pairBits (extractPrefix x,
  pairBits (extra x,pairBits (RawTake.run (pairBits (sampleCount x,raw x)),RawDrop.run (pairBits (sampleCount x,raw x)))))
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
noncomputable def repack_computes : PolyComputes repack := extractPrefix_computes.pair
  (extra_computes.pair (((sampleCount_computes.pair raw_computes).comp RawTake.run_computes).pair
    ((sampleCount_computes.pair raw_computes).comp RawDrop.run_computes)))
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryIntegralRecovery.run d ∘ repack
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := repack_computes.comp (BinaryIntegralRecovery.run_computes d)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) : List Bool := pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,pairBits (g,bits))
noncomputable def count {n : ℕ} (D : Finset (Fin n)) (Δ m : ℕ) : ℕ :=
  2*m*integralPrecision D (Δ:ℝ) m+BinaryRecovery.tapeSize (n+1)
noncomputable def layout {n : ℕ} (D : Finset (Fin n)) (Δ m : ℕ) :
    (Fin (count D Δ m)→Bool)≃(Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)×
      (Fin (BinaryRecovery.tapeSize (n+1))→Bool) :=
  (BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1))).trans
    (Equiv.prodCongr (BinarySeed.tensorEquiv [2*m] (integralPrecision D (Δ:ℝ) m)) (Equiv.refl _))
lemma layout_raw {n : ℕ} (D : Finset (Fin n)) (Δ m : ℕ) (bits : Fin (count D Δ m)→Bool) :
    BinarySeed.raw (ds:=[2*m]) (layout D Δ m bits).1++List.ofFn (layout D Δ m bits).2=List.ofFn bits := by
  change BinarySeed.raw (BinarySeed.tensorEquiv [2*m] (integralPrecision D (Δ:ℝ) m)
    ((BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1)) bits).1)) ++
      List.ofFn (BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1)) bits).2=_
  have hh := BinarySeed.raw_tensorEquiv [2*m] (integralPrecision D (Δ:ℝ) m)
    ((BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1)) bits).1)
  exact (congrArg (fun xs=>xs++List.ofFn (BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m)
    (BinaryRecovery.tapeSize (n+1)) bits).2) hh).trans (BinaryBranchTape.split_raw _ _ _)
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
include hm hΔ in
lemma sampleCount_pack : sampleCount (pack δ D F S Δ P m g bits)=(2*m*integralPrecision D (Δ:ℝ) m).bits := by
  have hp : params (pack δ D F S Δ P m g bits)=BinarySampler.Parameters.pack δ D F S Δ P m := by
    simp only [params,pack,extractPrefix_pairBits]
  simp only [sampleCount,mword,precision,Function.comp_apply,hp,
    (BinarySampler.Parameters.unary_pack δ D F S Δ P m hm hΔ).1,
    BinarySampler.Parameters.precision_pack δ D F S Δ P m hm hΔ,List.length_replicate]
include hm hΔ in
lemma repack_pack (seed : Fin (count D Δ m)→Bool) :
    repack (pack δ D F S Δ P m g (List.ofFn seed))=
      BinaryIntegralRecovery.pack δ D F S Δ P m g (layout D Δ m seed).1 (List.ofFn (layout D Δ m seed).2) := by
  rw [repack,sampleCount_pack δ D F S Δ P m g _ hm hΔ]
  simp only [pack,raw,extra,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    RawTake.run_pack,RawDrop.run_encode]
  rw [←layout_raw D Δ m seed]
  have hl : (BinarySeed.raw (ds:=[2*m]) (layout D Δ m seed).1).length=2*m*integralPrecision D (Δ:ℝ) m := by
    simpa only [List.cons_append,List.nil_append,List.prod_cons,List.prod_singleton,List.prod_nil,Nat.mul_one] using BinarySeed.raw_length (ds:=[2*m]) (layout D Δ m seed).1
  rw [←hl,List.take_left,List.drop_left]
  rfl
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool),
    run d (pack δ D F S Δ P m extra (List.ofFn seed))=
      BinaryFinSet.encode (result δ D F S Δ P m hm r0 y0 (layout D Δ m seed).1 (layout D Δ m seed).2) := by
  obtain ⟨d,hd⟩:=BinaryIntegralRecovery.run_source A
  refine ⟨d,?_⟩
  intro n δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 seed
  rw [run,Function.comp_apply,repack_pack δ D F S Δ P m extra hm hΔ]
  exact hd δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 _ _
lemma probability_layout (E : (Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)×
      (Fin (BinaryRecovery.tapeSize (n+1))→Bool)→Prop) :
    FiniteSampling.probability (fun seed=>E (layout D Δ m seed))=FiniteSampling.probability E :=
  FiniteSampling.probability_comp_equiv (layout D Δ m) E
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
