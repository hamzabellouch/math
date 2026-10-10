import Mathlib
import OAI.Computability.MinUncut.Graphs.DemandExpressions
import OAI.Computability.MinUncut.Estimates.UniformOutput

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncut.Outer MinUncut.Outer.LocalTemplate UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable {Q : ∀p,A p → Query (h p)} {pos : ∀p,A p → Fin (t p) → Fin 3}
variable (hQ : c.Map (Queries.queries t ht h hc) Q)
variable (hp : c.Map (Alphabet.positionsList t ht) pos)
include hp hc in
lemma O.secondAddress : O c (fun p x=>secondAddress (h p) (pos p x)) := by
  have hh : c.Map ((fin t ht).function bool) (fun p _=>h p) := map_const hc
  exact ((O.fixed (.mul ((AExpr.reg 1).pow 3) (.const 2))).pow (out_const c ht)).add
    (O.secondExpr ht hh hp)
include hQ hp in
lemma O.leftExpr : O c (fun p x=>leftExpr (Q p x) (pos p x)) := by
  let s:=Alphabet.signatures t ht
  have htab:=Queries.map_leftTable t ht h hc hQ.first hp.first (map_snd c s)
  have hnum : (c.prod s).Out (fun p x=>tableNumber ((Q p x.1).leftTable (pos p x.1) x.2)) :=
    (out_code ((Alphabet.ambient t ht).function bool)).comp htab
  have hl:=O.demandLookup ht hnum
  have hf:=map_comp hQ (Queries.map_first t ht h hc)
  have hfirst := O.fromC (c_firstExpr.precomp ht) (c:=c)
  have hsecond:=O.secondAddress t ht h hc hp
  exact hl.add ((O.const (out_const c (ca_pow (Computable.const 2)
    (ca_pow (Computable.const (2^3)) ht)))).mul (O.choose hf hfirst hsecond))
include hQ hp in
lemma O.rightExpr : O c (fun p x=>rightExpr (Q p x) (pos p x)) := by
  have htab:=Queries.map_rightTable t ht h hc hQ
  have hnum : c.Out (fun p x=>tableNumber (Q p x).rightTable) :=
    (out_code ((Alphabet.ambient t ht).function bool)).comp htab
  exact (O.const hnum).add ((O.const (out_const c (ca_pow (Computable.const 2)
    (ca_pow (Computable.const (2^3)) ht)))).mul (O.secondAddress t ht h hc hp))
include hQ hp in
lemma O.signExpr : O c (fun p x=>signExpr (Q p x) (pos p x)) := by
  let s:=Alphabet.signatures t ht
  have hs:=Queries.map_localSign t ht h hc hQ.first hp.first (map_snd c s)
  exact O.demandLookup ht (out_boolNat hs)
include hQ hp in
lemma out_queryExpressions : c.Out (fun p x=>
    ([leftExpr (Q p x) (pos p x),rightExpr (Q p x) (pos p x),signExpr (Q p x) (pos p x)]).map
      (fun e=>e.program.code)) :=
  (O.leftExpr t ht h hc hQ hp).cons ((O.rightExpr t ht h hc hQ hp).cons
    ((O.signExpr t ht h hc hQ hp).cons (out_const c (Computable.const []))))
end MinUncut.Preprocess.Syntax

end
end

end OAI
