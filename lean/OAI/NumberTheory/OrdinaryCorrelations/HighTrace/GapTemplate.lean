import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.OfRelabel
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapPathCode

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical
noncomputable section

abbrev GapTemplate (ℓ L J t m : ℕ) :=
  (Fin ℓ → Bool) × (Fin ℓ × Fin J → Option (Fin m)) ×
    (Fin t → GapPathCode ℓ L) × (Fin t → Fin m) × (Fin t → Fin m)

namespace GapTemplate
variable {ℓ L J t m : ℕ}
def selected (d : GapTemplate ℓ L J t m) := d.2.2.2.1
def modulus (d : GapTemplate ℓ L J t m) := d.2.2.2.2
def expression (d : GapTemplate ℓ L J t m) (h : ℕ) (i : Fin t) :=
  PatternExpression.gap h d.1 d.2.1 (d.2.2.1 i)

def WellFormed (d : GapTemplate ℓ L J t m) (h : ℕ) : Prop :=
  Function.Injective d.selected ∧
    (∀ i, d.modulus i≠d.selected i) ∧
    (∀ i j, i<j → d.selected j ∉ insert (d.modulus i) (d.expression h i).support)

def embedding (d : GapTemplate ℓ L J t m) (h : ℕ) (hd : d.WellFormed h) : Fin t ↪ Fin m :=
  ⟨d.selected,hd.1⟩
def system (d : GapTemplate ℓ L J t m) (h : ℕ) (hd : d.WellFormed h) :
    TriangularExpressions (d.embedding h hd) L where
  expression := d.expression h
  modulus := d.modulus
  linear _ := true
  divisor_modulus _ hi := Bool.noConfusion hi
  divisor_own_absent _ hi := Bool.noConfusion hi
  linear_modulus_ne i _ := hd.2.1 i
  future_absent := hd.2.2

lemma formed_of_relabel (d : GapTemplate ℓ L J t m) (h : ℕ)
    {α : Type*} [DecidableEq α] (v : Fin m ↪ α) (e : Fin t ↪ α)
    (q : TriangularExpressions e L) (hlin : ∀ i,q.linear i=true)
    (hs : ∀ i,v (d.selected i)=e i) (hm : ∀ i,v (d.modulus i)=q.modulus i)
    (he : ∀ i,(d.expression h i).relabel v=q.expression i) : d.WellFormed h := by
  have hi : Function.Injective d.selected := by
    intro i j hij
    apply e.injective
    rw [←hs i,←hs j,hij]
  let e' : Fin t ↪ Fin m := ⟨d.selected,hi⟩
  let q' := q.ofRelabel v e' hs (d.expression h) d.modulus he hm
  exact ⟨hi,fun i => q'.linear_modulus_ne i (hlin i),q'.future_absent⟩

lemma admissible_of_relabel (d : GapTemplate ℓ L J t m) (h : ℕ) (hd : d.WellFormed h)
    {α : Type*} [DecidableEq α] (v : Fin m ↪ α) (e : Fin t ↪ α)
    (q : TriangularExpressions e L) (hlin : ∀ i,q.linear i=true)
    (hs : ∀ i,v (d.selected i)=e i) (hm : ∀ i,v (d.modulus i)=q.modulus i)
    (he : ∀ i,(d.expression h i).relabel v=q.expression i)
    (P K : ℝ) (x : α → ℕ) (hx : q.Admissible P K x) :
    (d.system h hd).Admissible P K (fun a => x (v a)) := by
  intro i
  have hi := hx i
  dsimp only [TriangularExpressions.numericClause] at hi
  rw [ite_eq_left (hlin i)] at hi
  change (ArithmeticClause.linear ((d.expression h i).linearCoeff (d.selected i) (fun a => (x (v a):ℤ)))
    ((d.expression h i).constantTerm (d.selected i) (fun a => (x (v a):ℤ))) (x (v (d.modulus i)))).Holds P K (x (v (d.selected i)))
  rw [←SquarefreeExpression.linearCoeff_relabel (d.expression h i) v (fun a => (x a:ℤ)) (d.selected i),
    ←SquarefreeExpression.constant_relabel (d.expression h i) v (fun a => (x a:ℤ)) (d.selected i),hs i,hm i,he i]
  exact hi

lemma card (ℓ L J t m : ℕ) :
    Fintype.card (GapTemplate ℓ L J t m)=2^ℓ*(m+1)^(ℓ*J)*(2*ℓ+1)^(L*t)*m^(2*t) := by
  simp only [GapTemplate,GapPathCode,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Fintype.card_option]
  rw [←pow_mul]
  rw [show 2*t=t+t by omega,pow_add]
  simp only [show ℓ*2+1=2*ℓ+1 by omega]
  ring

end GapTemplate
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
