import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoverySuccess

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations Polynomial
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def completionCounter : PolynomialCounter (C 201326592000000015*(X+3)^12) := PolynomialCounter.choose _
noncomputable def sampleWord (x : List Bool) : List Bool := RepeatedAppend.copies (mword x++mword x).length (precision x)
noncomputable def sampleWord_computes : PolyComputes sampleWord := UnaryResources.copy_computes
  (mword_computes.append mword_computes) precision_computes
noncomputable def completionWord (x : List Bool) : List Bool := completionCounter.word (src 1 x)
noncomputable def completionWord_computes : PolyComputes completionWord := (src_computes 1).comp completionCounter.computes
noncomputable def demandWord (x : List Bool) : List Bool := sampleWord x++completionWord x
noncomputable def demandWord_computes : PolyComputes demandWord := sampleWord_computes.append completionWord_computes
noncomputable def demandBits : List Bool→List Bool := UnaryResources.lengthBits ∘ demandWord
noncomputable def demandBits_computes : PolyComputes demandBits := demandWord_computes.comp UnaryResources.lengthBits_computes
noncomputable def cut (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (extra x,
  RawTake.run (pairBits (demandBits x,raw x))))
attribute [local irreducible] extra raw demandBits RawTake.run
noncomputable def cut_computes : PolyComputes cut := extractPrefix_computes.pair
  (extra_computes.pair ((demandBits_computes.pair raw_computes).comp RawTake.run_computes))
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
include hm hΔ in
lemma demandWord_pack : (demandWord (pack δ D F S Δ P m g bits)).length=count D Δ m := by
  have hp : params (pack δ D F S Δ P m g bits)=BinarySampler.Parameters.pack δ D F S Δ P m := by
    simp only [params,pack,extractPrefix_pairBits]
  have hn : src 1 (pack δ D F S Δ P m g bits)=List.replicate n true := by
    simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,BinarySampler.Parameters.pack,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [demandWord,List.length_append,sampleWord,RepeatedAppend.length_copies,List.length_append,
    mword,precision]
  simp only [Function.comp_apply,hp]
  rw [
    (BinarySampler.Parameters.unary_pack δ D F S Δ P m hm hΔ).1,
    BinarySampler.Parameters.precision_pack δ D F S Δ P m hm hΔ]
  simp only [List.length_replicate,completionWord,hn,completionCounter.word_length,count,
    eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat,BinaryRecovery.tapeSize]
  congr 1; ring
include hm hΔ in
lemma demandBits_pack : demandBits (pack δ D F S Δ P m g bits)=(count D Δ m).bits := by
  rw [demandBits,Function.comp_apply,UnaryResources.lengthBits_eq,demandWord_pack δ D F S Δ P m g bits hm hΔ]
include hm hΔ in
lemma cut_pack : cut (pack δ D F S Δ P m g bits)=pack δ D F S Δ P m g (bits.take (count D Δ m)) := by
  rw [cut,demandBits_pack δ D F S Δ P m g bits hm hΔ]
  simp only [raw,extra,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack]
include hm hΔ in
lemma demand_polynomial : count D Δ m≤demandWord_computes.lengthPolynomial.eval (pack δ D F S Δ P m g []).length := by
  rw [←demandWord_pack δ D F S Δ P m g [] hm hΔ]
  exact demandWord_computes.length_bound _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Prefix
open WordOperations Sampling.Comparison
noncomputable def run (d : ℕ) : List Bool→List Bool := Fair.run d ∘ Fair.cut
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := Fair.cut_computes.comp (Fair.run_computes d)
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ {n K : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (hK : Fair.count D Δ m≤K) (seed : Fin K→Bool),
    run d (Fair.pack δ D F S Δ P m extra (List.ofFn seed))=
      BinaryFinSet.encode (result δ D F S Δ P m hm r0 y0
        (Fair.layout D Δ m (fun i=>seed (Fin.castLE hK i))).1
        (Fair.layout D Δ m (fun i=>seed (Fin.castLE hK i))).2) := by
  obtain ⟨d,hd⟩:=Fair.run_source A
  refine ⟨d,?_⟩
  intro n K δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 hK seed
  rw [run,Function.comp_apply,Fair.cut_pack δ D F S Δ P m extra _ hm hΔ,FiniteSampling.take_ofFn_cast hK]
  exact hd δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Prefix

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool) : Finset (Fin n) :=
  BinaryIntegralRecovery.result δ D F S Δ P m hm r0 y0 (layout D Δ m seed).1 (layout D Δ m seed).2
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool) :
    output δ D F S Δ P m hm r0 y0 seed⊆F ∧ (output δ D F S Δ P m hm r0 y0 seed).card=S.card ∧
      (output δ D F S Δ P m hm r0 y0 seed).Nonempty :=
  BinaryIntegralRecovery.result_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 _ _
lemma output_cost_le_start (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool) :
    realCost D (output δ D F S Δ P m hm r0 y0 seed)≤realCost D S :=
  BinaryIntegralRecovery.result_cost_le_start δ hδ D F S hSF hS Δ hbound P m hm r0 y0 _ _
lemma output_success (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hΔ : 1≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0<comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) :
    ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*
      ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))≤
      probability (fun seed:Fin (count D Δ C.bad.card)→Bool=>realCost D
        (output δ D F S Δ P C.bad.card hm r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  have hh:=BinaryIntegralRecovery.result_success δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0
  have he:=probability_comp_equiv (layout D Δ C.bad.card)
    (fun z=>realCost D (BinaryIntegralRecovery.result δ D F S Δ P C.bad.card hm r0 y0 z.1 z.2)≤
      (197/100:ℝ)*comparisonCost D C.assign)
  exact hh.trans_eq he.symm
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
lemma output_exponential : ∃ c : ℝ, 0<c ∧ ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (_hPeq : (P:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0<comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n),
    Real.exp (-c*C.bad.card)≤probability (fun seed:Fin (count D Δ C.bad.card)→Bool=>realCost D
      (output δ D F S Δ P C.bad.card hm r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  obtain ⟨c,hc,hsample⟩:=sampling_exponential
  obtain ⟨d,hd,hcompletion⟩:=completion_exponential
  refine ⟨c+d,add_pos hc hd,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0
  calc
    _=Real.exp (-c*C.bad.card)*Real.exp (-d*C.bad.card) := by rw [←Real.exp_add]; congr 1;ring
    _≤((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)) :=
      mul_le_mul (hsample C.bad.card) (hcompletion C.bad.card hm0) (Real.exp_nonneg _)
        ((Real.exp_nonneg _).trans (hsample C.bad.card))
    _≤_ := output_success δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
