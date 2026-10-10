import Mathlib
import OAI.Computability.MinUncut.Graphs.DemandQueryEffectivity

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.FiniteProof
lemma c_replicate {X : Type} [Primcodable X] : Computable₂ (fun n (x : X)=>List.replicate n x) := by
  have hf : Computable₂ (fun (x : X) (_ : ℕ)=>x) := Computable.fst
  have hh : Computable (fun p : ℕ × X=>(List.range p.1).map (fun _=>p.2)) :=
    (c_rangeMap hf).comp Computable.snd Computable.fst
  change Computable (fun p : ℕ × X=>List.replicate p.1 p.2)
  simpa using hh
attribute [local irreducible] rationalScoreTable MinUncut.FiniteGaussian.midpoint
namespace DemandBody
variable {P : Type} [Primcodable P] {p : P}
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def samples := ((Weights.localSamples t ht h hc m n hm hn hnpos g hg).prod (tests P)).prod
  (Alphabet.positionsList t ht)
def bodyQuery (σ η : ℚ) (x : (LocalSample (Alphabet (h p)) (m p) (n p) (g p) × Test) × (Fin (t p) → Fin 3)) :=
  query (h p) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
    (rationalScoreTable σ η (fun i=>midpoint (g p).T (g p).L (x.1.1.2.2.2 i))) x.1.2
lemma map_bodyScores (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    (samples t ht h hc m n hm hn hnpos g hg).Map
      ((Grid.indices m n hm hn hnpos).function UEncoding.bool)
      (fun p x=>rationalScoreTable (σ p) (η p) (fun i=>midpoint (g p).T (g p).L (x.1.1.2.2.2 i))) := by
  let s:=Weights.localSamples t ht h hc m n hm hn hnpos g hg
  let c:=(s.prod (tests P)).prod (Alphabet.positionsList t ht)
  have hs : c.Map s (fun _ x=>x.1.1) := (map_fst _ _).first
  have hq : c.Map (Grid.samples m n hm hn hnpos g hg) (fun _ x=>x.1.1.2.2.2) :=
    map_comp (map_comp (map_comp hs (map_snd _ _)) (map_snd _ _)) (map_snd _ _)
  have htable : (Grid.samples m n hm hn hnpos g hg).Map
      ((Grid.indices m n hm hn hnpos).function UEncoding.bool)
      (fun p q=>rationalScoreTable (σ p) (η p) (fun i=>midpoint (g p).T (g p).L (q i))) :=
    map_lambda (Grid.map_scoreTable m n hm hn hnpos g hg σ η hσ hη)
  exact map_comp (a:=c) (b:=Grid.samples m n hm hn hnpos g hg)
    (c:=(Grid.indices m n hm hn hnpos).function UEncoding.bool)
    (f:=fun _ x=>x.1.1.2.2.2)
    (g:=fun p q=>rationalScoreTable (σ p) (η p) (fun i=>midpoint (g p).T (g p).L (q i))) hq htable
lemma map_bodyQuery (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    (samples t ht h hc m n hm hn hnpos g hg).Map (Queries.queries t ht h hc)
      (fun p x=>bodyQuery t h m n g (σ p) (η p) x) := by
  let s:=Weights.localSamples t ht h hc m n hm hn hnpos g hg
  let c:=(s.prod (tests P)).prod (Alphabet.positionsList t ht)
  let ar:=Alphabet.arrays t ht h hc m n hm hn hnpos
  have hs : c.Map s (fun _ x=>x.1.1) := (map_fst _ _).first
  have hB : c.Map ar (fun _ x=>x.1.1.1) := map_comp hs (map_fst _ _)
  have hC : c.Map ar (fun _ x=>x.1.1.2.1) := map_comp (map_comp hs (map_snd _ _)) (map_fst _ _)
  have hz : c.Map (Face.codes m n hm hn hnpos) (fun _ x=>x.1.1.2.2.1) :=
    map_comp (map_comp (map_comp hs (map_snd _ _)) (map_snd _ _)) (map_fst _ _)
  have hj : c.Map (tests P) (fun _ x=>x.1.2) := (map_snd _ _).first
  exact Queries.map_query t ht h hc m n hm hn hnpos hB hC hz
    (map_bodyScores t ht h hc m n hm hn hnpos g hg σ η hσ hη) hj
lemma out_bodyExpressions (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    (samples t ht h hc m n hm hn hnpos g hg).Out (fun p x=>
      ([leftExpr (bodyQuery t h m n g (σ p) (η p) x) x.2,
        rightExpr (bodyQuery t h m n g (σ p) (η p) x) x.2,
        signExpr (bodyQuery t h m n g (σ p) (η p) x) x.2]).map (fun e=>e.program.code)) :=
  Syntax.out_queryExpressions t ht h hc (map_bodyQuery t ht h hc m n hm hn hnpos g hg σ η hσ hη)
    (map_snd _ _)
lemma out_bodyWeight (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j)) :
    (samples t ht h hc m n hm hn hnpos g hg).Out
      (fun p x=>localWeight (g p) (a p) (b p x.1.2) x.1.2 x.1.1) := by
  have hw:=(Weights.out_localWeight t ht h hc m n hm hn hnpos g hg a (fun _=>1) ha (ca_const 1)).first (b:=Alphabet.positionsList t ht)
  have hj : (samples t ht h hc m n hm hn hnpos g hg).Map (tests P) (fun _ x=>x.1.2) :=
    (map_snd _ _).first
  have hbud:=hb.comp hj
  apply (hw.ratDiv hbud).ofEq
  intro p x
  simp only [localWeight,div_one]
lemma out_bodyRepetitions (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j)) :
    (samples t ht h hc m n hm hn hnpos g hg).Out (fun p x=>
      multiplicity (innerDenominator (t p) (m p) (n p) (g p) (a p) (b p))
        (localWeight (g p) (a p) (b p x.1.2) x.1.2 x.1.1)) := by
  have hw := out_bodyWeight t ht h hc m n hm hn hnpos g hg a ha b hb
  have hd := out_const (samples t ht h hc m n hm hn hnpos g hg)
    (Denominator.c_innerDenominator t m n ht hm hn hnpos g hg a ha b hb)
  exact ((hw.map primrec_ratNum.to_comp).map primrec_intToNat.to_comp).map₂
    (hd.map₂ (hw.map primrec_ratDen.to_comp) Primrec.nat_div.to_comp) Primrec.nat_mul.to_comp
lemma out_repeatedExpressions (a : P → ℚ) (ha : Computable a)
    (b : P → Test → ℚ) (hb : (tests P).Out (fun p j=>b p j))
    (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    (samples t ht h hc m n hm hn hnpos g hg).Out (fun p x=>
      (List.replicate (multiplicity (innerDenominator (t p) (m p) (n p) (g p) (a p) (b p))
        (localWeight (g p) (a p) (b p x.1.2) x.1.2 x.1.1))
        (([leftExpr (bodyQuery t h m n g (σ p) (η p) x) x.2,
        rightExpr (bodyQuery t h m n g (σ p) (η p) x) x.2,
        signExpr (bodyQuery t h m n g (σ p) (η p) x) x.2]).map (fun e=>e.program.code))).flatten) := by
  exact ((out_bodyRepetitions t ht h hc m n hm hn hnpos g hg a ha b hb).map₂
    (out_bodyExpressions t ht h hc m n hm hn hnpos g hg σ η hσ hη)
    c_replicate).map Primrec.list_flatten.to_comp
end DemandBody
end MinUncut.Preprocess

end
end

end OAI
