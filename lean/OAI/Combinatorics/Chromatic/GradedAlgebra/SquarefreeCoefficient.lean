import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.OrderedIndependentProduct
import OAI.Combinatorics.Chromatic.Walls.SquarefreeBlocks

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section
lemma sum_eq_subtype {A R:Type*} [Fintype A] [AddCommMonoid R]
    (p:A → Prop) [DecidablePred p] (f:A → R) (hf:∀a,¬p a → f a=0) :
    ∑a,f a=∑a:{a // p a},f a.val := by
  rw [←Fintype.sum_subtype_add_sum_subtype p f]
  have H:(∑a:{a // ¬p a},f a.val)=0:=Finset.sum_eq_zero (fun a _=>hf a.val a.property)
  rw [H,add_zero]

namespace QuantumTorus
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ)
local instance squarefreeCoefficientRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance squarefreeCoefficientAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance squarefreeCoefficientAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
variable (c:(V → ℤ) →+ M) (hc:Function.Injective c)
variable {n r:ℕ} (b:Fin n ↪ V)

omit [Fintype V] in
lemma blockLabels_sum (s:Fin r → Finset V) :
    wordExponent (blockLabels (fun x=>c (Pi.single x 1)) s)=c (SquarefreeBlocks.vector s) := by
  simp only [wordExponent,blockLabels,SquarefreeBlocks.vector,map_sum]

include hc in
lemma independent_product_squarefree (a:Fin r → ℕ) :
    ((List.ofFn (fun i=>independentElement v Ω (fun x=>c (Pi.single x 1)) (a i))).prod)
        (c (SquarefreeBlocks.target b))=
      ∑κ:Fin n → Fin r,
        if BlockValid Ω (fun x=>c (Pi.single x 1)) a (SquarefreeBlocks.blocks b κ) then
          ↑(v^(wordEnergy Ω (blockLabels (fun x=>c (Pi.single x 1)) (SquarefreeBlocks.blocks b κ)))) else 0 := by
  rw [independentElement_product]
  have hs:∀(s:Finset (Fin r → Finset V)) (f:(Fin r → Finset V) → Torus v Ω),
      (∑a∈s,f a) (c (SquarefreeBlocks.target b))=∑a∈s,f a (c (SquarefreeBlocks.target b)):=by
    intro s f
    induction s using Finset.induction with
    | empty=>rfl
    | @insert a s ha ih=>
      rw [Finset.sum_insert ha,Finset.sum_insert ha]
      change f a _+(∑i∈s,f i) _=_
      rw [ih]
  rw [hs]
  let term (s:Fin r → Finset V):K:=
    (if BlockValid Ω (fun x=>c (Pi.single x 1)) a s then
      Torus.monomial v Ω (wordExponent (blockLabels (fun x=>c (Pi.single x 1)) s))
        (↑(v^(wordEnergy Ω (blockLabels (fun x=>c (Pi.single x 1)) s)))) else 0)
        (c (SquarefreeBlocks.target b))
  change (∑s,term s)=_
  rw [sum_eq_subtype (fun s=>SquarefreeBlocks.vector s=SquarefreeBlocks.target b) term]
  · rw [←Equiv.sum_comp (SquarefreeBlocks.equiv b).symm]
    apply Finset.sum_congr rfl
    intro κ hκ
    change term (SquarefreeBlocks.blocks b κ)=_
    unfold term
    split_ifs with h
    · rw [blockLabels_sum,Torus.monomial,SquarefreeBlocks.blocks_vector]
      exact Finsupp.single_eq_same
    · rfl
  · intro s hs
    unfold term
    split_ifs
    · rw [blockLabels_sum,Torus.monomial]
      exact Finsupp.single_eq_of_ne (fun h=>hs (hc h.symm))
    · rfl
end QuantumTorus
end
end ElementaryPositivity

end

end OAI
