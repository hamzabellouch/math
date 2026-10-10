import OAI.MathematicalPhysics.Heisenberg.SerialBlocks

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance meshCPDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open LayeredExchange
variable {V : Type} [Fintype V]

lemma cut_test_eq (n : ℕ) :
    (fun c : Fin (n+1)×V → Bool=>if (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))).card/4≤
      cutSpin (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))) c then (1:ℝ) else 0)=
    (fun c : Fin (n+1)×V → Bool=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization (fun v=>c (0,v)) then (1:ℝ) else 0) := by
  funext c
  rw [cut_card,cut_spin]

attribute [local irreducible] colorTail coinWiring layerWeight
lemma mesh_cut_product (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ) :
    colorTail (layerWeight rates) (coinWiring (finRotate (n+1)) a b)
      (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v)))=
    Matrix.trace (Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j))*
      Matrix.diagonal (fun c : V → Bool=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization c then (1:ℝ) else 0)) := by
  unfold colorTail
  rw [cut_test_eq]
  exact mesh_trace_product n a b rates (fun c : V → Bool=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization c then (1:ℝ) else 0)

lemma mesh_partition_product (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ) :
    Heisenberg.Pin.pinPartition (layerWeight rates) (coinWiring (finRotate (n+1)) a b) ∅=
    Matrix.trace (Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j))) := by
  rw [pinPartition_empty_trace]
  have hh:=mesh_trace_product n a b rates (fun _=>1)
  simpa only [Matrix.diagonal_one,Matrix.mul_one] using hh

end Heisenberg.Surface
end
end

end OAI
