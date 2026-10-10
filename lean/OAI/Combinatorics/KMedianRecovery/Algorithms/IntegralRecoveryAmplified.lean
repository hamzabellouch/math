import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryRepeat
import OAI.Combinatorics.KMedianRecovery.Sampling.MetricBestProbability

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n) (t : ℕ) (seed : Fin t→Fin (Fair.count D Δ m)→Bool) :
    output δ D F S Δ P m hm r0 y0 t seed⊆F ∧ (output δ D F S Δ P m hm r0 y0 t seed).card=S.card ∧
      (output δ D F S Δ P m hm r0 y0 t seed).Nonempty := by
  apply BinaryMetricBest.best_property δ D S _ (fun U=>U⊆F ∧ U.card=S.card ∧ U.Nonempty) ⟨hSF,rfl,hS⟩
  intro U hU
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
  exact Fair.output_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 (seed i)
lemma amplified (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
    {B p ζ : ℝ} (hB : 0≤B) (hp : 0<p)
    (hsuccess : p≤probability (fun seed:Fin (Fair.count D Δ m)→Bool=>realCost D
      (Fair.output δ D F S Δ P m hm r0 y0 seed)≤B)) (hζ : 0<ζ)
    (t : ℕ) (ht : Real.log (1/ζ)/p≤(t:ℝ)) :
    (∀ seed:Fin t→Fin (Fair.count D Δ m)→Bool,realCost D (output δ D F S Δ P m hm r0 y0 t seed)≤realCost D S) ∧
    1-ζ≤probability (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed)≤B) ∧
    average (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed))≤B+realCost D S*ζ := by
  exact BinaryMetricBest.amplified δ hδ D S hS (Fair.output δ D F S Δ P m hm r0 y0)
    (fun seed=>(Fair.output_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 seed).2.2)
    hB (by rw [realCost,dite_eq_left hS]; exact Finset.sum_nonneg (fun _ _=>distanceTo_nonneg _ _ _)) le_rfl hp hsuccess hζ t ht
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
open Polynomial
lemma polynomial_program (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (_hPeq : (P:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0<comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) (N : ℕ) (g : List Bool)
    (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
      run Q d (Fair.pack δ D F S Δ P C.bad.card g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
        BinaryFinSet.encode (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)) ∧
    (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
      output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed⊆F ∧
      (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).card=S.card ∧
      (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).Nonempty) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
        realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
          (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
      realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed))≤
        (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨c,hc,hexp⟩:=Fair.output_exponential
  obtain ⟨K,b,hb⟩:=LogPolynomial.amplification_polynomial c A IntegralAssembly.gamma e hc.le IntegralAssembly.gamma_pos
  obtain ⟨d,hd⟩:=run_source A
  let Q : Polynomial ℕ:=Polynomial.C K*(X+2)^b
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound P hPeq hsep hP hm0 hm r0 y0 N g hN hlog
  have hcount : ⌈Real.log (1/FailureBudget.failure IntegralAssembly.gamma e N)/
      Real.exp (-c*C.bad.card)⌉₊≤Q.eval g.length := by
    apply (hb N C.bad.card hlog).trans
    simp only [Q,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat]
    exact Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.add_le_add_right hN 2) b)
  have ht : Real.log (1/FailureBudget.failure IntegralAssembly.gamma e N)/Real.exp (-c*C.bad.card)≤((Q.eval g.length:ℕ):ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcount)
  have hh:=amplified δ hδ D F S hSF hS Δ hbound P C.bad.card hm r0 y0
    (by positivity : (0:ℝ)≤(197/100:ℝ)*comparisonCost D C.assign) (Real.exp_pos _)
    (hexp δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0)
    (FailureBudget.failure_pos IntegralAssembly.gamma_pos e N) (Q.eval g.length) ht
  exact ⟨hd Q δ D F S Δ P C.bad.card hm hcap g N hN hlog r0 y0,
    output_feasible δ hδ D F S hSF hS Δ hbound P C.bad.card hm r0 y0 _,hh.2⟩
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
attribute [local irreducible] Repeat.run Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
noncomputable def demandWord (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RepeatedAppend.copies (Repeat.rword Q x).length (Repeat.bword x)
noncomputable def demandWord_computes (Q : Polynomial ℕ) : PolyComputes (demandWord Q) :=
  UnaryResources.copy_computes (Repeat.rword_computes Q) Repeat.bword_computes
noncomputable def demandBits (Q : Polynomial ℕ) : List Bool→List Bool := UnaryResources.lengthBits ∘ demandWord Q
noncomputable def demandBits_computes (Q : Polynomial ℕ) : PolyComputes (demandBits Q) :=
  (demandWord_computes Q).comp UnaryResources.lengthBits_computes
attribute [local irreducible] demandBits
noncomputable def cut (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (extra x,RawTake.run (pairBits (demandBits Q x,Fair.raw x))))
noncomputable def cut_computes (Q : Polynomial ℕ) : PolyComputes (cut Q) :=
  extractPrefix_computes.pair (extra_computes.pair (((demandBits_computes Q).pair Fair.raw_computes).comp RawTake.run_computes))
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := Repeat.run Q d ∘ cut Q
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (cut_computes Q).comp (Repeat.run_computes Q d)
variable {n : ℕ}
lemma demandWord_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g raw : List Bool) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    (demandWord Q (Fair.pack δ D F S Δ P m g raw)).length=Q.eval g.length*Fair.count D Δ m := by
  rw [demandWord,RepeatedAppend.length_copies]
  have hr : (Repeat.rword Q (Fair.pack δ D F S Δ P m g raw)).length=Q.eval g.length := by
    simp only [Repeat.rword,RawUnary.run,List.length_replicate,Repeat.counter,PolynomialCounter.word_length,
      extra,Fair.pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  have hb : (Repeat.bword (Fair.pack δ D F S Δ P m g raw)).length=Fair.count D Δ m := by
    simp only [Repeat.bword,Function.comp_apply,RawUnary.run,List.length_replicate,
      Fair.demandWord_pack δ D F S Δ P m g raw hm hΔ]
  rw [hr,hb]
lemma cut_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g raw : List Bool) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    cut Q (Fair.pack δ D F S Δ P m g raw)=Fair.pack δ D F S Δ P m g
      (raw.take (Q.eval g.length*Fair.count D Δ m)) := by
  have hh : demandBits Q (Fair.pack δ D F S Δ P m g raw)=(Q.eval g.length*Fair.count D Δ m).bits := by
    rw [demandBits,Function.comp_apply,UnaryResources.lengthBits_eq,demandWord_pack Q δ D F S Δ P m g raw hm hΔ]
  rw [cut,hh]
  simp only [extra,Fair.raw,Fair.pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack]
lemma demand_polynomial (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g : List Bool) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    Q.eval g.length*Fair.count D Δ m≤(demandWord_computes Q).lengthPolynomial.eval
      (Fair.pack δ D F S Δ P m g []).length := by
  rw [←demandWord_pack Q δ D F S Δ P m g [] hm hΔ]
  exact (demandWord_computes Q).length_bound _
def layout (t b : ℕ) : (Fin (t*b)→Bool)≃(Fin t→Fin b→Bool) :=
  BinarySeed.tensorEquiv [t] b
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ (Q : Polynomial ℕ) {n K : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (g : List Bool) (N : ℕ),
    N≤g.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (hK : Q.eval g.length*Fair.count D Δ m≤K) (seed : Fin K→Bool),
    run Q d (Fair.pack δ D F S Δ P m g (List.ofFn seed))=
      BinaryFinSet.encode (Repeat.output δ D F S Δ P m hm r0 y0 (Q.eval g.length)
        (layout (Q.eval g.length) (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i)))) := by
  obtain ⟨d,hd⟩:=Repeat.run_source A
  refine ⟨d,?_⟩
  intro Q n K δ D F S Δ P m hm hΔ g N hN hlog r0 y0 hK seed
  rw [run,Function.comp_apply,cut_pack Q δ D F S Δ P m g _ hm hΔ,take_ofFn_cast hK]
  have hr:=BinarySeed.raw_tensorEquiv [Q.eval g.length] (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i))
  change BinarySeed.raw (ds:=[Q.eval g.length]) (layout (Q.eval g.length) (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i)))=_ at hr
  exact (congrArg (fun raw=>Repeat.run Q d (Fair.pack δ D F S Δ P m g raw)) hr).symm.trans
    (hd Q δ D F S Δ P m hm hΔ g N hN hlog r0 y0 _)
lemma probability_layout {t b K : ℕ} (hK : t*b≤K) (E : (Fin t→Fin b→Bool)→Prop) :
    probability (fun seed:Fin K→Bool=>E (layout t b (fun i=>seed (Fin.castLE hK i))))=probability E :=
  (probability_prefix hK (fun z=>E (layout t b z))).trans (probability_comp_equiv (layout t b) E)
lemma average_layout {t b K : ℕ} (hK : t*b≤K) (X : (Fin t→Fin b→Bool)→ℝ) :
    average (fun seed:Fin K→Bool=>X (layout t b (fun i=>seed (Fin.castLE hK i))))=average X := by
  exact (average_precompose_embedding ⟨Fin.castLE hK,Fin.castLE_injective hK⟩ (fun z=>X (layout t b z))).trans
    (average_equiv (layout t b) _ _ (fun _=>rfl))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape

end OAI
