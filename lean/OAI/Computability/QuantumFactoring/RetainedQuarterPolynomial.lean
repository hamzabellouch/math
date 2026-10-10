import Mathlib
import OAI.Computability.QuantumFactoring.RetainedQuarterFilter
import OAI.Computability.QuantumFactoring.TreePreparationPolynomial
import OAI.Computability.QuantumFactoring.RetainedPrefixPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma factorVerifierBound_at {α : Type*} {len n c : α→ℕ}
    (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>factorVerifierBound (n x) (c x)) := by
  have hr:=PolyAt.comp rootWidth_poly hn
  have hp:=PolyAt.comp primalityBound_poly hn
  have hprod:= (hn.mul ((((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 105).mul hn)).add
    (PolyAt.const len 21)).add hr).add (((PolyAt.const len 90).mul hr).mul hr)).add
    ((PolyAt.const len 14).mul hr)).add (PolyAt.const len 6))).add hr
  have hfirst:= (hn.mul (((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 146).mul hn)).add
    (PolyAt.const len 35)).add hr).add hp).add (PolyAt.const len 1))).add (PolyAt.const len 1)
  have hsecond:= ((hn.mul hn).mul ((((PolyAt.const len 4).mul hc).add
    ((PolyAt.const len 242).mul hn)).add (PolyAt.const len 58))).add (PolyAt.const len 1)
  exact ((((hfirst.add hsecond).add (PolyAt.const len 1)).add
    ((((hprod.add hc).add hr).add ((PolyAt.const len 96).mul hr)).add (PolyAt.const len 21))).add
      (PolyAt.const len 1))
lemma physicalResultBound : PolyBound PhysicalNode.resultBound := by
  exact (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
    (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
end PreparationPolynomial
namespace NodeMachine
lemma rowBound_at {α : Type*} {len n c : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (hq : NetworkAt len (fun x=>(M x).query)) :
    PolyAt len (fun x=>(M x).rowBound) := by
  have hr:=PolyAt.comp PreparationPolynomial.physicalResultBound hn
  exact (((PolyAt.add hq ((PolyAt.const len 97).mul hn)).add (PolyAt.const len 25)).add
    (PreparationPolynomial.factorVerifierBound_at hn (PolyAt.add hq hr)))
lemma verifiedNet_at {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).verifiedNet (t x)) :=
  NetworkAt.of_le ((ht.mul ((rowBound_at hn hq).add (PolyAt.const len 1))).add (PolyAt.const len 1))
    (fun x=>(M x).verifiedNet_count (t x))
lemma acceptedNet_at {α : Type*} {len c t : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).acceptedNet (hpos x) (t x)) :=
  (verifiedNet_at (PolyAt.self len) ht hq).band
    (treePrefixFilter_at hpos ht ht hq (NetworkAt.select (fun _=>id)))
end NodeMachine
namespace PhysicalTree
lemma padFlag_poly : NetworkPoly padFlag := by
  unfold padFlag
  exact NetworkAt.all_ofFn PreparationPolynomial.treePadding
    (((NetworkAt.select _).zeroWord (PolyAt.self (fun xi:Σn,Fin (padding n)=>xi.1))).bnot)
lemma paddedFlag_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>paddedFlag (len x) (hpos x)) := by
  have ht : PolyAt len (fun x=>2*(len x)^2):=(PolyAt.const len 2).mul ((PolyAt.self len).pow 2)
  have hq : NetworkAt len (fun x=>(machine (len x)).query):=NetworkAt.ofPoly PreparationPolynomial.treeQuery len
  have ha:=NodeMachine.acceptedNet_at hpos ht hq
  exact (((NetworkAt.select _).comp (NetworkAt.select _)).comp ha).band
    ((NetworkAt.select _).comp (NetworkAt.ofPoly padFlag_poly len))
lemma guessVerifier_poly : NetworkPoly guessVerifier := by
  apply NetworkAt.of_le (PreparationPolynomial.factorVerifierBound_at (PolyAt.self id) (PolyAt.const id 0))
  intro n
  exact factorVerifierOn_count _ _ (by simp only [count_select,le_refl]) (by intro i;simp only [count_select,le_refl])
lemma quarterGuessFlag_poly : NetworkPoly quarterGuessFlag :=
  ((((NetworkAt.select _).comp ((NetworkAt.select _).comp (NetworkAt.select _))).pair
    (NetworkAt.select _)).comp guessVerifier_poly)
lemma quarterRare_poly : NetworkPoly quarterRare :=
  ((NetworkAt.select _).zeroWord (PolyAt.const id 1))
lemma quarterKeep_poly {p : ℕ→ℚ} (hp : RatHeightPoly p) :
    NetworkPoly (fun n=>quarterKeep n (p n)) := by
  unfold quarterKeep
  exact retentionNet_at Quarter.D_poly (RatExprPoly.ofHeight hp) (NatExprPoly.var (fun _=>()))
    Quarter.D_poly ⟨0,fun n i=>by simp only [quarterCoin,Completion.retentionWires,count_select,Polynomial.eval_zero,le_refl]⟩
lemma quarterFlag_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    NetworkAt len (fun x=>quarterFlag (len x) (hpos x)) := by
  have hr:=NetworkAt.ofPoly quarterRare_poly len
  have hp:=paddedFlag_at len hpos
  have hk:=NetworkAt.ofPoly (quarterKeep_poly Quarter.retention_height) len
  have hg:=NetworkAt.ofPoly (quarterKeep_poly Quarter.guessRetention_height) len
  have hv:=NetworkAt.ofPoly quarterGuessFlag_poly len
  exact (hr.bnot.band (((NetworkAt.select _).comp hp).band hk)).bor (hr.band (hv.band hg))
end PhysicalTree
end ExactQuantumFactoring

end



end OAI
