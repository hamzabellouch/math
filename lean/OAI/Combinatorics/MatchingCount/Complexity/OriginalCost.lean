import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.AlgorithmLaw
import OAI.Combinatorics.MatchingCount.Complexity.ComputeCost

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

lemma count_cost (a : Parsed) : countRealizer.cost a=
    (pair emptyRealizer identity).cost a+
      (if empty a then (constant ((1,1) : Fraction)).cost a else
        (pair invalidRealizer identity).cost a+
          (if invalid a then (constant ((0,1) : Fraction)).cost a else computeRealizer.cost a)+30)+30 := by
  simp only [countRealizer,OnlineTree.Realizer.congr,OnlineTree.conditional,
    OnlineTree.composition,OnlineTree.deterministic,Experiment.worst,OnlineTree.caseBool,id_eq]
  split <;> omega
lemma algorithm_cost (as : List Symbol) : algorithmRealizer.cost as=
    parseInputRealizer.cost as+countRealizer.cost (parseInput as)+
      (count (parseInput as)).worst LiteralCodec.ratWordRealizer.cost := rfl
lemma algorithm_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) (ε δ : ℚ)
    (_he : 0<ε) (_he1 : ε<1) (_hd : 0≤δ) (x : ℕ),1≤x→
    (encodeInput G ε δ).length≤x→⌈ε⁻¹⌉₊≤x→Nat.clog 2 ⌈δ⁻¹⌉₊≤x→
    algorithmRealizer.cost (encodeInput G ε δ)+(algorithm (encodeInput G ε δ)).worst weight≤q.eval x := by
  obtain ⟨p,hp⟩:=polynomial_parseInput
  obtain ⟨e,he⟩:=polynomial_pair polynomial_empty polynomial_identity
  obtain ⟨j,hj⟩:=polynomial_pair polynomial_invalid polynomial_identity
  obtain ⟨c,hc⟩:=polynomial_constant ((1,1) : Fraction) (A:=Parsed)
  obtain ⟨d,hd⟩:=polynomial_constant ((0,1) : Fraction) (A:=Parsed)
  obtain ⟨k,hk⟩:=compute_bound
  obtain ⟨v,hv⟩:=LiteralCodec.polynomial_ratWord
  let P:=p.comp (18*X+1)
  let B:Polynomial ℕ:=2*X+P+1
  let Q:=e.comp P+j.comp P+c.comp P+d.comp P+k.comp B+60
  refine ⟨P+Q+2*(v.comp Q),?_⟩
  intro G ε δ hε hε1 hδ x hx hl hεx hδx
  let as:=encodeInput G ε δ
  let a:=parseInput as
  have hparse : parseInputRealizer.cost as+weight a≤P.eval x := by
    apply (hp as).trans
    rw [LiteralCodec.weight_word]
    simpa only [P,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one] using
      polynomial_eval_monotone p (show 18*as.length+1≤18*x+1 by dsimp only [as];omega)
  have hwa : weight a≤P.eval x := by omega
  have hep : (pair emptyRealizer identity).cost a≤e.eval (P.eval x) :=
    (Nat.le_add_right _ _).trans ((he a).trans (polynomial_eval_monotone e hwa))
  have hjp : (pair invalidRealizer identity).cost a≤j.eval (P.eval x) :=
    (Nat.le_add_right _ _).trans ((hj a).trans (polynomial_eval_monotone j hwa))
  have hcp : (constant ((1,1) : Fraction)).cost a+weight ((1,1) : Fraction)≤c.eval (P.eval x) :=
    (hc a).trans (polynomial_eval_monotone c hwa)
  have hdp : (constant ((0,1) : Fraction)).cost a+weight ((0,1) : Fraction)≤d.eval (P.eval x) :=
    (hd a).trans (polynomial_eval_monotone d hwa)
  have hb : x≤B.eval x ∧ 2*x≤B.eval x ∧ P.eval x≤B.eval x := by
    simp only [B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hcount : countRealizer.cost a+(count a).worst weight≤Q.eval x := by
    cases hE:empty a with
    | true =>
      rw [count_cost]
      simp only [count,hE,ite_true,Experiment.worst,Q,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_ofNat]
      omega
    | false =>
      cases hI:invalid a with
      | true =>
        rw [count_cost]
        simp only [count,hE,hI,Bool.false_eq_true,ite_false,ite_true,Experiment.worst,Q,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_ofNat]
        omega
      | false =>
        have hn:=valid_two G ε δ hE hI
        have hev:=valid_even G ε δ hI
        let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
        have hnx : G.n≤B.eval x := (valid_size G ε δ hI).trans ((Nat.mul_le_mul_left 2 hl).trans hb.2.1)
        have hcompute:=hk G hn hev ε δ hε hε1 hδ (B.eval x) (hx.trans hb.1) hnx (hεx.trans hb.1) (hδx.trans hb.1) (hwa.trans hb.2.2)
        rw [count_cost]
        simp only [count,hE,hI,Bool.false_eq_true,ite_false,Q,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_ofNat]
        dsimp only [as,a] at *
        omega
  have hout : (count a).All (fun z=>LiteralCodec.ratWordRealizer.cost z+weight (LiteralCodec.ratWord z)≤v.eval (Q.eval x)) :=
    (Experiment.all_worst (count a) weight).mono (fun z hz=>(hv z).trans
      (polynomial_eval_monotone v (hz.trans (by omega))))
  have htail : (count a).worst LiteralCodec.ratWordRealizer.cost≤v.eval (Q.eval x) :=
    Experiment.worst_le _ _ _ (hout.mono (fun z hz=>(Nat.le_add_right _ _).trans hz))
  have hword : (count a).worst (weight ∘ LiteralCodec.ratWord)≤v.eval (Q.eval x) :=
    Experiment.worst_le _ _ _ (hout.mono (fun z hz=>(Nat.le_add_left _ _).trans hz))
  rw [algorithm_cost]
  unfold algorithm
  rw [Experiment.worst_map]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  dsimp only [a,as] at *
  omega
end MatchingFPRAS.LiteralAlgorithm

end OAI
