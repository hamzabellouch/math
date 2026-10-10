import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.OnlineInitialDataCost
import OAI.Combinatorics.MatchingCount.Algorithm.Algorithm
import OAI.Combinatorics.MatchingCount.Complexity.OnlineRunCost
import OAI.Combinatorics.MatchingCount.Machines.OnlineBounds

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream Polynomial OnlineSourceBounds LiteralInput

lemma initialize_materialize {G : GraphInput} [Nontrivial (Fin G.n)]
    (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ) :
    OnlineInitial.initializeInput (materialize (parseInput (encodeInput G ε δ)))=
      (2*Amplification.halfRepetitions δ+1,
        OnlineTrial.initial (reorder G) (FiniteTrial.parameters G hn hev ε he he1)) := by
  rw [materialize_source,OnlineGraph.initialize_eq,
    OnlineInitial.initializeInput_source hn hev ε δ he he1 hd]
  rfl
lemma numeric_materialize (G : GraphInput) (ε δ : ℚ) :
    OnlineInitial.configNumeric (OnlineInitial.config (materialize (parseInput (encodeInput G ε δ))))=
      OnlineInitial.configNumeric (OnlineInitial.config (OnlineInitial.sourceSeed (G:=G) ε δ)) := by
  rw [materialize_source]
  rfl
lemma materialize_vertices (G : GraphInput) (ε δ : ℚ) :
    (materialize (parseInput (encodeInput G ε δ))).1.1.length=G.n := by
  rw [LiteralInput.parseInput_source];simp only [materialize,List.length_range]
lemma materialize_epsilon (G : GraphInput) (ε δ : ℚ) :
    (materialize (parseInput (encodeInput G ε δ))).2.1=TreeFraction.repr ε := by
  rw [LiteralInput.parseInput_source];rfl
lemma graph_weight_materialize (G : GraphInput) (ε δ : ℚ) :
    weight (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))≤
      weight (materialize (parseInput (encodeInput G ε δ))) := by
  rw [materialize_source]
  change weight _≤weight (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G),_)
  rw [weight_prod (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))]
  omega

lemma compute_cost (a : Parsed) : computeRealizer.cost a=
    materializeRealizer.cost a+OnlineInitial.initializeInputRealizer.cost (materialize a)+
      OnlineAmplification.runRealizer.cost (OnlineInitial.initializeInput (materialize a)) := rfl

lemma compute_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (_hn : 2≤G.n) (_hev : Even G.n) (ε δ : ℚ) (_he : 0<ε) (_he1 : ε<1) (_hd : 0≤δ)
    (x : ℕ),1≤x→G.n≤x→⌈ε⁻¹⌉₊≤x→Nat.clog 2 ⌈δ⁻¹⌉₊≤x→
    weight (parseInput (encodeInput G ε δ))≤x→
    computeRealizer.cost (parseInput (encodeInput G ε δ))+
      (compute (parseInput (encodeInput G ε δ))).worst weight≤q.eval x := by
  obtain ⟨m,hm⟩:=work_materialize
  obtain ⟨i,hi⟩:=OnlineInitial.work_initializeInput
  obtain ⟨r,hr⟩:=OnlineAmplification.run_bound
  obtain ⟨b,hb⟩:=polynomial_bound normBound_polynomial
  let M:=m.comp (2*X)
  let S:Polynomial ℕ:=2*X+b+M
  let R:Polynomial ℕ:=11*X+11+b+M
  refine ⟨M+i.comp S+r.comp R,?_⟩
  intro G inst hn hev ε δ he he1 hd x hx hnx hex hdx hwx
  let a:=parseInput (encodeInput G ε δ)
  let seed:=materialize a
  let p:=FiniteTrial.parameters G hn hev ε he he1
  have hn2:G.n≤2*x := by omega
  have ha:a.1=G.n := by dsimp only [a];rw [LiteralInput.parseInput_source]
  have hmat:materializeRealizer.cost a+weight seed≤M.eval x := by
    apply (hm a).trans
    apply (polynomial_eval_monotone m (show a.1+weight a≤2*x by dsimp only [a] at *;omega)).trans
    simp only [M,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X];rfl
  have hseed:OnlineInitial.seedSize seed≤S.eval x := by
    have hnum:OnlineInitial.configNumeric (OnlineInitial.config seed)≤b.eval x := by
      dsimp only [seed,a]
      rw [numeric_materialize]
      exact (numeric_le hn hev ε δ he he1 x hn2 hex).trans (hb x hx)
    have hlen:(seed.1.1).length=G.n:=materialize_vertices G ε δ
    have hep:natCeil (inverse seed.2.1)=⌈ε⁻¹⌉₊ := by
      rw [show seed.2.1=TreeFraction.repr ε from materialize_epsilon G ε δ,inverse_repr ε he.le,natCeil_repr _ (inv_nonneg.mpr he.le)]
    simp only [OnlineInitial.seedSize,hlen,hep,S,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have hini:OnlineInitial.initializeInputRealizer.cost seed ≤ i.eval (S.eval x) :=
    (Nat.le_trans (Nat.le_add_right _ _) (hi seed)).trans (polynomial_eval_monotone i hseed)
  have hnorm:OnlineTrial.sizeNorm p (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))≤b.eval x+M.eval x := by
    apply (norm_le hn hev ε he he1 x hn2 hex _).trans
    have hg:=graph_weight_materialize G ε δ
    have hnb:=hb x hx
    dsimp only [seed,a] at hmat
    omega
  have hrep:2*Amplification.halfRepetitions δ+1≤10*x+11:=by
    rw [Amplification.repetitions_source];omega
  have harg:2*Amplification.halfRepetitions δ+1+
      OnlineTrial.sizeNorm p (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))≤R.eval x := by
    simp only [R,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have hrun:= (hr G (reorder G) (reorder_mem G) p (2*Amplification.halfRepetitions δ+1)).trans
    (polynomial_eval_monotone r harg)
  have hinput:=initialize_materialize hn hev ε δ he he1 hd
  rw [compute_cost]
  unfold compute
  rw [hinput]
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  dsimp only [a,seed,p] at hini hmat hrun
  omega
end MatchingFPRAS.LiteralAlgorithm

end OAI
