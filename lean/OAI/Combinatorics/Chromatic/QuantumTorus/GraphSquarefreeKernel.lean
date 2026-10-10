import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousElementaryExpressions
import OAI.Combinatorics.Chromatic.Model
import OAI.Combinatorics.Chromatic.GradedAlgebra.SquarefreeCoefficient
import OAI.Combinatorics.Chromatic.QuantumTorus.OrdinaryElementaryExpressions
import OAI.Combinatorics.Chromatic.Walls.GraphBlockPairing

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {n r:ℕ} (G:NaturalUnitIntervalGraph n)
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance graphSquarefreeKernelRing : Ring (Torus v Ω) := Torus.instRing v Ω
variable (c:(V → ℤ) →+ M) (hc:Function.Injective c) (b:Fin n ↪ V)
variable (hp:∀i j,i < j → Ω (c (Pi.single (b i) 1)) (c (Pi.single (b j) 1))= -(if G.Edge i j then 1 else 0))

include hΩ hc hp in
lemma graph_squarefree_kernel (a:Fin r → ℕ) :
    ((List.ofFn (fun i=>independentElement v Ω (fun x=>c (Pi.single x 1)) (a i))).prod)
        (c (SquarefreeBlocks.target b))=
      ∑κ:Fin n → Fin r,
        if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
          ↑(v^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))) else 0 := by
  rw [independent_product_squarefree v Ω c hc b]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [G.blockValid_iff Ω hΩ _ b hp]
  split_ifs with h
  · rw [G.blocks_energy Ω hΩ _ b hp κ h.1]
  · rfl
end
end ElementaryPositivity.NaturalUnitIntervalGraph

end
section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section

def ElementaryExpr.sequence : (a:List ℕ) → ElementaryExpr a.sum
  | []=>.one
  | k::a=>.mul (.atom k) (sequence a)

variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)
local instance graphSquarefreeSequenceRing : Ring (Torus v Ω) := Torus.instRing v Ω
lemma ElementaryExpr.sequence_eval (u:V → M) (a:List ℕ) :
    (sequence a).eval v Ω u=(a.map (independentElement v Ω u)).prod := by
  induction a with
  | nil=>rfl
  | cons k a ih=>change independentElement v Ω u k*(sequence a).eval v Ω u=_; rw [ih]; rfl
lemma ElementaryExpr.eval_cast {N K:ℕ} (h:N=K) (f:ElementaryExpr N) (u:V → M) :
    (h ▸ f).eval v Ω u=f.eval v Ω u := by subst K; rfl
variable {R σ:Type*} [CommRing R] [Fintype σ]
lemma ElementaryExpr.sequence_ordinary (a:List ℕ) :
    (sequence a).ordinary (σ:=σ) (R:=R)=(a.map (MvPolynomial.esymm σ R)).prod := by
  induction a with
  | nil=>rfl
  | cons k a ih=>change MvPolynomial.esymm σ R k*(sequence a).ordinary=_; rw [ih]; rfl

lemma ElementaryExpr.sequence_ofFn_eval (u:V → M) {r:ℕ} (a:Fin r → ℕ) :
    (sequence (List.ofFn a)).eval v Ω u=(List.ofFn (fun i=>independentElement v Ω u (a i))).prod := by
  rw [sequence_eval,List.map_ofFn]
  rfl
lemma ElementaryExpr.sequence_ofFn_ordinary {r:ℕ} (a:Fin r → ℕ) :
    (sequence (List.ofFn a)).ordinary (σ:=σ) (R:=R)=∏i:Fin r,MvPolynomial.esymm σ R (a i) := by
  rw [sequence_ordinary,List.map_ofFn,List.prod_ofFn]
  rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
