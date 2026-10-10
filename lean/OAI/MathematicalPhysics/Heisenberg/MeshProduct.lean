import OAI.MathematicalPhysics.Heisenberg.MeshSurface

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance meshProductDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open LayeredExchange
variable {V : Type} [Fintype V]

lemma transport_matrix_prefix (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (k : ℕ) :
    SlotColor.matrix (transport (finRotate (n+1)) σ 0 k)=
      MeshPair.prefixMatrix (fun j : ℕ=>SlotColor.matrix (σ (j : Fin (n+1)))) k := by
  induction k with
  | zero=>exact SlotColor.matrix_one
  | succ k ih=>rw [transport_succ_zero,SlotColor.matrix_mul,MeshPair.prefixMatrix,ih]

lemma transport_matrix_product (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) :
    SlotColor.matrix (transport (finRotate (n+1)) σ 0 (n+1))=
      Serial.product (n+1) (fun j=>SlotColor.matrix (σ j)) := by
  rw [transport_matrix_prefix]
  have hh:=Serial.prefix_product (fun j : ℕ=>SlotColor.matrix (σ (j : Fin (n+1)))) (n+1)
  with_reducible convert hh using 1; congr! 10
  simp

def colorCoin (a b : V) (r : ℝ) : Matrix (V → Bool) (V → Bool) ℝ :=
  (1-r) • 1+r • SlotColor.matrix (Equiv.swap a b)

lemma mean_transport (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ) :
    (∑ c : Fin (n+1) → Bool,layerWeight rates c •
      SlotColor.matrix (transport (finRotate (n+1)) (fun t=>if c t then Equiv.swap (a t) (b t) else 1) 0 (n+1)))=
    Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j)) := by
  simp_rw [transport_matrix_product]
  unfold layerWeight
  have hh:=Serial.mean_product (V:=V → Bool) (n+1)
    (fun (j : Fin (n+1)) (z : Bool)=>if z then rates j else 1-rates j)
    (fun j z=>SlotColor.matrix (if z then Equiv.swap (a j) (b j) else 1))
  change _=_ at hh
  with_reducible convert hh using 1 <;> congr! 5
  all_goals simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false,SlotColor.matrix_one,colorCoin]
  all_goals first | rfl | exact add_comm _ _

lemma trace_mean_test {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ)
    (M : Ω → Matrix V V ℝ) (D : Matrix V V ℝ) :
    (∑ ω,μ ω*Matrix.trace (M ω*D))=Matrix.trace ((∑ ω,μ ω • M ω)*D) := by
  simp only [Finset.sum_mul,Matrix.smul_mul,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul]

theorem mesh_trace_product (n : ℕ) (a b : Fin (n+1) → V) (rates : Fin (n+1) → ℝ)
    (f : (V → Bool) → ℝ) :
    (∑ c : Fin (n+1) → Bool,layerWeight rates c * Matrix.trace
      (SlotColor.matrix (coinWiring (finRotate (n+1)) a b c)*Matrix.diagonal (fun x=>f (fun v=>x (0,v)))))=
    Matrix.trace (Serial.product (n+1) (fun j=>colorCoin (a j) (b j) (rates j))*Matrix.diagonal f) := by
  unfold coinWiring
  simp_rw [trace_wiring_cut]
  rw [trace_mean_test,mean_transport]

end Heisenberg.Surface
end
end

end OAI
