import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralRecoveryGuesses

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
lemma run_of_repeat {n K : ℕ} (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) (g : List Bool)
    (r0 y0 : Fin n) (hK : Q.eval g.length*Fair.count D Δ m≤K)
    (hrun : ∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ m)→Bool,
      Repeat.run Q d (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
        BinaryFinSet.encode (Repeat.output δ D F S Δ P m hm r0 y0 (Q.eval g.length) seed))
    (seed : Fin K→Bool) :
    run Q d (Fair.pack δ D F S Δ P m g (List.ofFn seed))=
      BinaryFinSet.encode (Repeat.output δ D F S Δ P m hm r0 y0 (Q.eval g.length)
        (layout (Q.eval g.length) (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i)))) := by
  rw [run,Function.comp_apply,cut_pack Q δ D F S Δ P m g _ hm hΔ,take_ofFn_cast hK]
  have hr:=BinarySeed.raw_tensorEquiv [Q.eval g.length] (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i))
  change BinarySeed.raw (ds:=[Q.eval g.length]) (layout (Q.eval g.length) (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i)))=_ at hr
  exact (congrArg (fun raw=>Repeat.run Q d (Fair.pack δ D F S Δ P m g raw)) hr).symm.trans (hrun _)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
noncomputable def output (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) : Finset (Fin n) :=
  BinarySanitizedBest.output δ D F S S.card (words Q d δ D F S Δ g raw)
lemma run_output (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    run Q d (pack δ D F S Δ g raw)=BinaryFinSet.encode (output Q d δ D F S Δ g raw) :=
  run_pack Q d δ D F S Δ g raw hΔ
lemma output_feasible (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool) :
    output Q d δ D F S Δ g raw⊆F ∧ (output Q d δ D F S Δ g raw).Nonempty ∧
      (output Q d δ D F S Δ g raw).card≤S.card :=
  BinarySanitizedBest.output_feasible δ D F S S.card _ hSF hS le_rfl
variable [PseudoMetricSpace (Fin n)]
lemma cost_le_start (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool) :
    realCost D (output Q d δ D F S Δ g raw)≤realCost D S :=
  BinarySanitizedBest.realCost_le_self δ hδ D F S S.card _ hSF hS le_rfl
lemma cost_le_designated (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool)
    (p m : ℕ) (hp : p≤D.card*Δ) (hm : m≤n) (U : Finset (Fin n))
    (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤S.card)
    (hrun : Repeat.FiniteTape.run Q d (Fair.pack δ D F S Δ p m g raw)=BinaryFinSet.encode U) :
    realCost D (output Q d δ D F S Δ g raw)≤realCost D U := by
  apply BinarySanitizedBest.realCost_le_good δ hδ D F S S.card _ hSF hS le_rfl U hUF hU hUk
  rw [←hrun]
  exact word_mem Q d δ D F S Δ g raw p m hp hm
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
attribute [local irreducible] atInput choices Repeat.FiniteTape.demandWord
noncomputable def atDemand (Q : Polynomial ℕ) : List Bool→List Bool := Repeat.FiniteTape.demandWord Q ∘ atInput
noncomputable def atDemand_computes (Q : Polynomial ℕ) : PolyComputes (atDemand Q) :=
  atInput_computes.comp (Repeat.FiniteTape.demandWord_computes Q)
noncomputable def demandWords (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  mapWith (atDemand Q) (pairBits (x,choices x))
attribute [local irreducible] mapWith
noncomputable def demandWords_computes (Q : Polynomial ℕ) : PolyComputes (demandWords Q) :=
  PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atDemand Q))
    (id_computes.pair choices_computes) (mapWith_computes (atDemand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demandWords_computes Q).lengthPolynomial
variable {n : ℕ}
lemma demandWords_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    demandWords Q (pack δ D F S Δ g raw)=encode
      ((List.ofFn (fun p:Fin (D.card*Δ+1)=>p)).flatMap (fun p=>List.ofFn (fun m:Fin (n+1)=>
        Repeat.FiniteTape.demandWord Q (Fair.pack δ D F S Δ p.val m.val g raw)))) := by
  rw [demandWords,choices,(ranges_pack δ D F S Δ g raw hΔ).1,(ranges_pack δ D F S Δ g raw hΔ).2,
    cross_encode,mapWith_encode]
  simp only [flatMap_ofFn,List.map_flatten,List.map_ofFn,Function.comp_def,atDemand,atInput_pack]
lemma budget_bound (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (p m : ℕ) (hp : p≤D.card*Δ) (hm : m≤n) :
    Q.eval g.length*Fair.count D Δ m≤(budget Q).eval (pack δ D F S Δ g []).length := by
  have hh : Repeat.FiniteTape.demandWord Q (Fair.pack δ D F S Δ p m g []) ∈
      (List.ofFn (fun p:Fin (D.card*Δ+1)=>p)).flatMap (fun p=>List.ofFn (fun m:Fin (n+1)=>
        Repeat.FiniteTape.demandWord Q (Fair.pack δ D F S Δ p.val m.val g []))) :=
    List.mem_flatMap.mpr ⟨⟨p,Nat.lt_succ_of_le hp⟩,List.mem_ofFn.mpr ⟨⟨p,Nat.lt_succ_of_le hp⟩,rfl⟩,
      List.mem_ofFn.mpr ⟨⟨m,Nat.lt_succ_of_le hm⟩,rfl⟩⟩
  have hb:=length_member_le_encode hh
  rw [Repeat.FiniteTape.demandWord_pack Q δ D F S Δ p m g [] hm hΔ,
    ←demandWords_pack Q δ D F S Δ g [] hΔ] at hb
  exact hb.trans ((demandWords_computes Q).length_bound _)
lemma all_counts_budget (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (m : ℕ) (hm : m≤n) :
    Q.eval g.length*Fair.count D Δ m≤(budget Q).eval (pack δ D F S Δ g []).length :=
  budget_bound Q δ D F S Δ g hΔ 0 m (Nat.zero_le _) hm
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output Repeat.output budget Fair.pack Repeat.FiniteTape.layout

lemma polynomial_recovery (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (p : ℕ) (_hp : p≤D.card*Δ) (_hPeq : (p:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0<comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (_hm : C.bad.card≤n) (_r0 _y0 : Fin n) (N : ℕ) (g : List Bool)
    (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    let K := (budget Q).eval (pack δ D F S Δ g []).length
    (∀ seed:Fin K→Bool,run Q d (pack δ D F S Δ g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δ D F S Δ g (List.ofFn seed))) ∧
    (∀ seed:Fin K→Bool,output Q d δ D F S Δ g (List.ofFn seed)⊆F ∧
      (output Q d δ D F S Δ g (List.ofFn seed)).Nonempty ∧
      (output Q d δ D F S Δ g (List.ofFn seed)).card≤S.card ∧
      realCost D (output Q d δ D F S Δ g (List.ofFn seed))≤realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin K→Bool=>realCost D (output Q d δ D F S Δ g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→Bool=>realCost D (output Q d δ D F S Δ g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨Q,d,hd⟩:=Repeat.polynomial_program A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound p hp hPeq hsep hP hm0 hm r0 y0 N g hN hlog
  dsimp only
  have hPeq' : ((p:ℚ):ℝ)=comparisonCost D C.assign := by simpa only [Rat.cast_natCast] using hPeq
  obtain ⟨hrun,hfeas,hprob,havg⟩:=hd δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound p hPeq'
    hsep hP hm0 hm r0 y0 N g hN hlog
  have hK:=all_counts_budget Q δ D F S Δ g hcap C.bad.card hm
  let Θ := (budget Q).eval (pack δ D F S Δ g []).length
  let trial (seed : Fin Θ→Bool) : Finset (Fin n) := Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length)
    (Repeat.FiniteTape.layout (Q.eval g.length) (Fair.count D Δ C.bad.card) (fun i=>seed (Fin.castLE hK i)))
  have hdom (seed : Fin Θ→Bool) : realCost D (output Q d δ D F S Δ g (List.ofFn seed))≤realCost D (trial seed) := by
    have hf:=hfeas (Repeat.FiniteTape.layout (Q.eval g.length) (Fair.count D Δ C.bad.card) (fun i=>seed (Fin.castLE hK i)))
    apply cost_le_designated Q d δ hδ D F S hSF hS Δ g (List.ofFn seed) p C.bad.card hp hm (trial seed)
      hf.1 hf.2.2 hf.2.1.le
    exact Repeat.FiniteTape.run_of_repeat Q d δ D F S Δ p C.bad.card hm hcap g r0 y0 hK hrun seed
  refine ⟨fun _=>run_output Q d δ D F S Δ g _ hcap,?_,?_,?_⟩
  · intro seed
    have hf:=output_feasible Q d δ D F S hSF hS Δ g (List.ofFn seed)
    exact ⟨hf.1,hf.2.1,hf.2.2,cost_le_start Q d δ hδ D F S hSF hS Δ g _⟩
  · have hh : probability (fun seed:Fin Θ→Bool=>realCost D (trial seed)≤(197/100:ℝ)*comparisonCost D C.assign)=
        probability (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
            (197/100:ℝ)*comparisonCost D C.assign) := Repeat.FiniteTape.probability_layout hK (fun seed=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
            (197/100:ℝ)*comparisonCost D C.assign)
    exact (hprob.trans_eq hh.symm).trans (probability_mono (fun seed hs=>(hdom seed).trans hs))
  · have hh : average (fun seed:Fin Θ→Bool=>realCost D (trial seed))=
        average (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed)) :=
      Repeat.FiniteTape.average_layout hK (fun seed=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed))
    exact (average_mono hdom).trans (hh.le.trans havg)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
