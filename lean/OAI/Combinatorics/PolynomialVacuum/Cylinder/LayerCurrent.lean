import OAI.Combinatorics.PolynomialVacuum.Geometry.HoneycombLocalFlow
import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenIce

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ} [NeZero M]

 

noncomputable def layerValues (out inp aux internal : ZMod M → Spin) (e : Edge M) : ℤ :=
  if e.1.2=0 then
    if e.2=0 then -charge (inp e.1.1) else
    if e.2=1 then -charge (internal e.1.1) else charge (aux e.1.1)
  else if e.1.2=1 ∧ e.2=0 then -charge (out e.1.1) else 0

noncomputable def layerEdges (M : ℕ) [NeZero M] : Finset (Edge M) :=
  (Finset.univ ×ˢ ({0,1} : Finset ℤ)) ×ˢ Finset.univ

noncomputable def layerCurrent (out inp aux internal : ZMod M → Spin) : Edge M →₀ ℤ :=
  Finsupp.onFinset (layerEdges M) (layerValues out inp aux internal) (by
    intro e he
    have hj : e.1.2=0 ∨ e.1.2=1 := by
      by_contra hh
      have hz : e.1.2≠0 ∧ e.1.2≠1 := by tauto
      exact he (by simp [layerValues,hz.1,hz.2])
    simpa [layerEdges] using hj)

@[simp] theorem layerCurrent_apply (out inp aux internal : ZMod M → Spin) (e : Edge M) :
    layerCurrent out inp aux internal e=layerValues out inp aux internal e := rfl

theorem layer_up (out inp aux internal : ZMod M → Spin) (i : ZMod M) (k : Fin 3) :
    orientedFlow (layerCurrent out inp aux internal) (.up i 0,k)=
      arrowTriple (-charge (inp i)) (-charge (internal i)) (charge (aux i)) k := by
  rw [orientedFlow_up]
  simp [layerValues,arrowTriple]

theorem layer_down (out inp aux internal : ZMod M → Spin) (i : ZMod M) (k : Fin 3) :
    orientedFlow (layerCurrent out inp aux internal) (.down i 0,k)=
      arrowTriple (charge (out i)) (charge (internal i)) (-charge (aux (i+1))) k := by
  rw [orientedFlow_down]
  fin_cases k <;> simp [layerValues,arrowTriple,edgeOf]

theorem layer_up_ice (out inp aux internal : ZMod M → Spin) (i : ZMod M) :
    LocalIce (layerCurrent out inp aux internal) (.up i 0) ↔
      charge (aux i)=charge (internal i)+charge (inp i) := by
  unfold LocalIce
  simp_rw [layer_up]
  exact up_ice _ _ _

theorem layer_down_ice (out inp aux internal : ZMod M → Spin) (i : ZMod M) :
    LocalIce (layerCurrent out inp aux internal) (.down i 0) ↔
      charge (aux (i+1))=charge (internal i)+charge (out i) := by
  unfold LocalIce
  simp_rw [layer_down]
  exact down_ice _ _ _

noncomputable def localCurrentWeight (q : Edge M →₀ ℤ) (v : Vertex M) : ℂ :=
  arrowVertexWeight (orientedFlow q (v,0)) (orientedFlow q (v,1)) (orientedFlow q (v,2))

theorem layer_piece_weight (out inp aux internal : ZMod M → Spin) (i : ZMod M) :
    honeycombPiece (out i,aux i) (aux (i+1),inp i) (internal i)=
      localCurrentWeight (layerCurrent out inp aux internal) (.up i 0)*
      localCurrentWeight (layerCurrent out inp aux internal) (.down i 0)*
      anglePhase (5*(charge (aux (i+1))-charge (aux i))) := by
  rw [honeycombPiece_arrows]
  simp [localCurrentWeight,layer_up,layer_down,arrowTriple]

private theorem angle_product {α : Type*} [Fintype α] (f : α → ℤ) :
    ∏i,anglePhase (f i)=anglePhase (∑i,f i) := by
  classical
  have hh : ∀ s : Finset α,∏i∈s,anglePhase (f i)=anglePhase (∑i∈s,f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha,ih]
  exact hh Finset.univ

theorem layer_weight_telescopes (out inp aux internal : ZMod M → Spin) :
    (∏i : ZMod M,honeycombPiece (out i,aux i) (aux (i+1),inp i) (internal i))=
      ∏i : ZMod M,localCurrentWeight (layerCurrent out inp aux internal) (.up i 0)*
        localCurrentWeight (layerCurrent out inp aux internal) (.down i 0) := by
  simp_rw [layer_piece_weight]
  rw [Finset.prod_mul_distrib,angle_product]
  have hs : (∑i : ZMod M,charge (aux (i+1)))=∑i : ZMod M,charge (aux i) := by
    exact Equiv.sum_comp (Equiv.addRight (1 : ZMod M)) (fun i => charge (aux i))
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,hs,sub_self,mul_zero,anglePhase_zero,mul_one]

end PolynomialVacuumCylinder

end OAI
