import Mathlib
import OAI.Combinatorics.Chromatic.Histories.TriangularCommonHistory
import OAI.Combinatorics.Chromatic.Walls.GraphTriangularEmbedding
import OAI.Combinatorics.Chromatic.QuantumTorus.GraphSquarefreeKernel
import OAI.Combinatorics.Chromatic.Walls.ElementaryMatrixDuality

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n D:ℕ}

def graphVertex (b:Fin n ↪ Cell D) : Fin n ↪ Vertex D (Cell D):=
  ⟨fun i=>Sum.inr (b i),fun _ _ h=>b.injective (Sum.inr.inj h)⟩

lemma squarefree_weight (b:Fin n ↪ Vertex D (Cell D)) :
    vertexWeight (SquarefreeBlocks.target b)=(n:ℤ) := by
  simp only [SquarefreeBlocks.target,map_sum]
  have H:∀i:Fin n,vertexWeight (Pi.single (b i) (1:ℤ))=1:=by
    intro i
    simp [vertexWeight_apply,Pi.single_apply]
  simp only [H,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma squarefree_rootDegree (b:Fin n ↪ Vertex D (Cell D)) :
    ∃d,HasRootDegree (extendedRoots D) d
      (includeVertices (SquarefreeBlocks.target b)-triangularBase n) := by
  obtain ⟨d,c,hc,he⟩:=triangularVertex_rootDegree (SquarefreeBlocks.target b) (fun a=>by
    rw [SquarefreeBlocks.target_apply]
    split_ifs <;> omega)
  refine ⟨d,c,hc,?_⟩
  change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=_
  change forwardRoots (fun i=>(c i:ℤ))=_ at he
  rw [he,squarefree_weight,map_sub]
  rfl

lemma graphVertex_pair (G:NaturalUnitIntervalGraph n) (b:Fin n ↪ Cell D)
    (hb:∀i j,i < j → bridgePositive (b j) (b i)=(if G.Edge i j then 1 else 0) ∧
      bridgePositive (b i) (b j)=0) (i j:Fin n) (hij:i < j) :
    extendedOmega D (includeVertices (Pi.single (graphVertex b i) 1))
      (includeVertices (Pi.single (graphVertex b j) 1))= -(if G.Edge i j then 1 else 0) := by
  rw [extendedOmega_original]
  change matrixPairing (chartMatrix cellLevel triangularBB)
    (Pi.single (.inr (b i)) 1) (Pi.single (.inr (b j)) 1)=_
  rw [matrixPairing_single]
  change triangularBB (b i) (b j)=_
  rw [triangularBB,(hb i j hij).1,(hb i j hij).2,zero_sub]

theorem graph_common_history (G:NaturalUnitIntervalGraph n) :
    ∃D:ℕ,∃p:LocalHistoryFormula (Extended (Vertex D (Cell D)))
      ((Vertex D (Cell D) → ℝ) × (Vertex D (Cell D) → ℝ)),
      p.Positive (extendedOmega D) (extendedRoots D) extendedCast
        (simpleTotalTransport (extendedOmega D) (extendedRoots D)) ∧
      ∀(r:ℕ) (a:Fin r →₀ ℕ),a.degree=n →
        (∑κ:Fin n → Fin r,
          if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
            (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
        ∑l:{l:p.Leaf // AnchoredLeaf n p l},
          p.leafWeight (extendedOmega D) (extendedRoots D) extendedCast
            (simpleTotalTransport (extendedOmega D) (extendedRoots D)) l.val *
          (∏i:Fin (D+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ) (leafProfile n p l i)).coeff a := by
  obtain ⟨D,b,hb⟩:=graph_triangular_embedding G
  obtain ⟨d,hd⟩:=squarefree_rootDegree (graphVertex b)
  obtain ⟨p,hp,hbound,he⟩:=triangular_common_history n d _ hd
  refine ⟨D,p,hp,?_⟩
  intro r a ha
  have hs:(List.ofFn (fun i=>a i)).sum=n:=by
    rw [List.sum_ofFn]
    have H:=Finsupp.sum_fintype a (fun _ k=>k) (fun _=>rfl)
    exact H.symm.trans ha
  let f:ElementaryExpr n:=hs ▸ ElementaryExpr.sequence (List.ofFn (fun i=>a i))
  have hf:triangularExpression f=
      (List.ofFn (fun i=>independentElement LaurentRay.vUnit (extendedOmega D)
        (fun x=>includeVertices (Pi.single x 1)) (a i))).prod := by
    unfold triangularExpression f
    rw [ElementaryExpr.eval_cast,ElementaryExpr.sequence_ofFn_eval]
    rw [show vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)=
      (fun x:Vertex D (Cell D)=>includeVertices (Pi.single x 1)) from funext initial_vertexDisplay]
  have hfo:f.ordinary (σ:=Fin (D+1)) (R:=LaurentSeries ℚ)=
      ∏i:Fin r,MvPolynomial.esymm (Fin (D+1)) (LaurentSeries ℚ) (a i):=by
    dsimp [f]
    rw [ElementaryExpr.ordinary_cast,ElementaryExpr.sequence_ofFn_ordinary]
  rw [←G.graph_squarefree_kernel LaurentRay.vUnit (extendedOmega D) extendedOmega_self
    includeVertices includeVertices_injective (graphVertex b) (graphVertex_pair G b hb),←hf,he f]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hfo,ElementaryMatrix.duality]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
