import OAI.MathematicalPhysics.Heisenberg.MeshCutProduct

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance completionDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open LayeredExchange MeshPair
variable {V : Type} [Fintype V]

def completedEndpoint (a u : ℕ → V) (q c : ℕ) (j : ℕ) : V :=
  if j%(q+c)<q then a (j%(q+c)) else u (j%(q+c)-q)

def completedRate (δ : ℝ) (q c k : ℕ) (j : ℕ) : ℝ :=
  if j%(q+c)<q then δ/2 else if k*(q+c)≤j then 1 else 0

@[simp] lemma colorCoin_zero (a b : V) : colorCoin a b 0=1 := by simp [colorCoin]
@[simp] lemma colorCoin_one (a b : V) : colorCoin a b 1=SlotColor.matrix (Equiv.swap a b) := by simp [colorCoin]

lemma completed_product (a b u v : ℕ → V) (q c k : ℕ) (δ : ℝ) :
    Serial.product ((k+1)*(q+c)) (fun j=>colorCoin
      (completedEndpoint a u q c j) (completedEndpoint b v q c j) (completedRate δ q c k j))=
    prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c*
      (prefixMatrix (fun j=>colorCoin (a j) (b j) (δ/2)) q)^(k+1) := by
  let Q:=q+c
  let A:=fun j=>colorCoin (a j) (b j) (δ/2)
  let P:=fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))
  rw [←Serial.prefix_product (fun j=>colorCoin
    (completedEndpoint a u q c j) (completedEndpoint b v q c j) (completedRate δ q c k j))]
  rw [←Serial.completed_sweeps A P q c k]
  apply Serial.prefix_congr
  intro j hj
  change j<(k+1)*Q at hj
  rw [Nat.add_mul,Nat.one_mul] at hj
  change colorCoin _ _ _=(if j<k*Q then _ else _)
  by_cases hearly : j<k*Q
  · rw [ite_eq_left hearly]
    by_cases hsp : j%Q<q
    · simp only [completedEndpoint,completedRate,Q] at hsp ⊢
      rw [ite_eq_left hsp,ite_eq_left hsp,ite_eq_left hsp,ite_eq_left hsp]
    · simp only [completedEndpoint,completedRate,Q] at hsp ⊢
      rw [ite_eq_right hsp,ite_eq_right hsp,ite_eq_right hsp,ite_eq_right hsp,ite_eq_right (show ¬k*(q+c)≤j from by change ¬k*Q≤j; omega)]
      exact colorCoin_zero _ _
  · rw [ite_eq_right hearly]
    have hrem : j%Q=j-k*Q := by
      have hlt : j-k*Q<Q := by omega
      have hdecomp : j=k*Q+(j-k*Q):=by omega
      conv_lhs=>rw [hdecomp]
      rw [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt hlt]
    by_cases hsp : j-k*Q<q
    · simp only [completedEndpoint,completedRate,show q+c=Q from rfl,hrem,ite_eq_left hsp,A]
    · simp only [completedEndpoint,completedRate,show q+c=Q from rfl,hrem,ite_eq_right hsp,
        ite_eq_left (by omega : k*Q≤j),colorCoin_one,P]

lemma completed_rate_bounds (q c k j : ℕ) {δ : ℝ} (hδ : 0≤δ) (hδ2 : δ≤2) :
    0≤completedRate δ q c k j ∧ completedRate δ q c k j≤1 := by
  unfold completedRate
  split_ifs <;> constructor <;> linarith

end Heisenberg.Surface
end
end

end OAI
