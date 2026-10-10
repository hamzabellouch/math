import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryDemand

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw Fair.demandWord Fair.run BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter Q := PolynomialCounter.choose Q
noncomputable def rword (Q : Polynomial ℕ) (x : List Bool) : List Bool := RawUnary.run ((counter Q).word (extra x))
noncomputable def rword_computes (Q : Polynomial ℕ) : PolyComputes (rword Q) :=
  (extra_computes.comp (counter Q).computes).comp RawUnary.run_computes
noncomputable def bword : List Bool→List Bool := RawUnary.run ∘ Fair.demandWord
noncomputable def bword_computes : PolyComputes bword := Fair.demandWord_computes.comp RawUnary.run_computes
noncomputable def rows (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  BinarySeed.rows (pairBits (encode [rword Q x,bword x],Fair.raw x))
noncomputable def rows_computes (Q : Polynomial ℕ) : PolyComputes (rows Q) :=
  ((cons_computes (rword_computes Q) (cons_computes bword_computes (const_computes []))).pair Fair.raw_computes).comp
    BinarySeed.rows_computes
noncomputable def context (x : List Bool) : List Bool := pairBits (extractPrefix x,extra x)
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.pair extra_computes
noncomputable def atSeedInput (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),
  pairBits (discardPrefix (extractPrefix x),discardPrefix x))
noncomputable def atSeedInput_computes : PolyComputes atSeedInput := (extractPrefix_computes.comp extractPrefix_computes).pair
  ((extractPrefix_computes.comp discardPrefix_computes).pair discardPrefix_computes)
noncomputable def atSeed (d : ℕ) : List Bool→List Bool := Fair.run d ∘ atSeedInput
noncomputable def atSeed_computes (d : ℕ) : PolyComputes (atSeed d) := atSeedInput_computes.comp (Fair.run_computes d)
noncomputable def candidates (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (atSeed d) (pairBits (context x,rows Q x))
attribute [local irreducible] mapWith
noncomputable def candidates_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidates Q d) :=
  PolyComputes.comp (f := fun input=>pairBits (context input,rows Q input)) (g := mapWith (atSeed d))
    (context_computes.pair (rows_computes Q)) (mapWith_computes (atSeed_computes d))
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  BinaryMetricBest.run (pairBits (metricContext x,pairBits (src 4 x,candidates Q d x)))
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (metricContext_computes.pair ((src_computes 4).pair (candidates_computes Q d))).comp BinaryMetricBest.run_computes
lemma run_of_candidates (Q : Polynomial ℕ) (d : ℕ) (data : List Bool) {n : ℕ}
    (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (hmetric : metricContext data=BinaryMetricBest.context δ D)
    (hS : src 4 data=BinaryFinSet.encode S)
    (hxs : candidates Q d data=encode (xs.map BinaryFinSet.encode)) :
    run Q d data=BinaryFinSet.encode (BinaryMetricBest.best δ D S xs) := by
  rw [run,hmetric,hS,hxs]
  exact BinaryMetricBest.run_pack δ D S xs
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (r0 y0 : Fin n) (t : ℕ) (seed : Fin t→Fin (Fair.count D Δ m)→Bool) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i)))
lemma rows_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) (g : List Bool)
    (seed : Fin (Q.eval g.length)→Fin (Fair.count D Δ m)→Bool) :
    rows Q (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
      encode (List.ofFn (fun i=>List.ofFn (seed i))) := by
  have hr : rword Q (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
      List.replicate (Q.eval g.length) true := by
    simp only [rword,RawUnary.run,PolynomialCounter.word_length,extra,Fair.pack,Function.comp_apply,
      extractPrefix_pairBits,discardPrefix_pairBits]
  have hb : bword (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
      List.replicate (Fair.count D Δ m) true := by
    rw [bword,Function.comp_apply,RawUnary.run,Fair.demandWord_pack δ D F S Δ P m g _ hm hΔ]
  rw [rows,hr,hb]
  simp only [Fair.raw,Fair.pack,Function.comp_apply,discardPrefix_pairBits]
  exact BinarySeed.rows_tensor seed
lemma candidates_of_rows (Q : Polynomial ℕ) (d : ℕ) (data ctx : List Bool) {t b n : ℕ}
    (seed : Fin t→Fin b→Bool) (f : Fin t→Finset (Fin n))
    (hr : rows Q data=encode (List.ofFn (fun i=>List.ofFn (seed i))))
    (hx : context data=ctx)
    (hf : ∀ i,atSeed d (pairBits (ctx,List.ofFn (seed i)))=BinaryFinSet.encode (f i)) :
    candidates Q d data=encode ((List.ofFn f).map BinaryFinSet.encode) := by
  rw [candidates,hr,hx,mapWith_ofFn,List.map_ofFn]
  exact congrArg encode (congrArg List.ofFn (funext hf))
lemma atSeed_pack {n : ℕ} (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g bits : List Bool) :
    atSeed d (pairBits (pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,g),bits))=
      Fair.run d (Fair.pack δ D F S Δ P m g bits) := by
  simp only [atSeed,Function.comp_apply,atSeedInput,extractPrefix_pairBits,discardPrefix_pairBits,Fair.pack]
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ (Q : Polynomial ℕ) {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (seed : Fin (Q.eval extra.length)→Fin (Fair.count D Δ m)→Bool),
    run Q d (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      BinaryFinSet.encode (output δ D F S Δ P m hm r0 y0 (Q.eval extra.length) seed) := by
  obtain ⟨d,hd⟩:=Fair.run_source A
  refine ⟨d,?_⟩
  intro Q n δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 seed
  have hx : context (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,extra) := by
    simp only [context,Fair.pack,BinaryIntegralRecovery.extra,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  have hc : candidates Q d (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      encode ((List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i))).map BinaryFinSet.encode) := by
    apply candidates_of_rows Q d _ _ seed _ (rows_pack Q δ D F S Δ P m hm hΔ extra seed) hx
    intro i
    rw [atSeed_pack]
    simpa only [Fair.output] using hd δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 (seed i)
  have hmtr : metricContext (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=BinaryMetricBest.context δ D := by
    simp only [metricContext,src,Fair.pack,Function.comp_apply,extractPrefix_pairBits,
      BinarySampler.Parameters.pack,BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinaryMetricBest.context]
  have hs : src 4 (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=BinaryFinSet.encode S := by
    simp only [src,Fair.pack,Function.comp_apply,extractPrefix_pairBits,BinarySampler.Parameters.pack,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [output]
  exact run_of_candidates Q d _ δ D S (List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i))) hmtr hs hc
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
