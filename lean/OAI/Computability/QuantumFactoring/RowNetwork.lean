import Mathlib
import OAI.Computability.QuantumFactoring.BooleanVector
import OAI.Computability.QuantumFactoring.BitNumbers
import OAI.Computability.QuantumFactoring.TriangularAlgebra

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

def rowIndex {b : ℕ} (j e : Fin b) : Fin b :=
  ⟨(b-1+j.val-e.val)%b, Nat.mod_lt _ (by have := j.isLt; omega)⟩

lemma rowIndex_val {b : ℕ} (j e : Fin b) (h : j.val ≤ e.val) :
    (rowIndex j e).val = b-1+j.val-e.val := by
  apply Nat.mod_eq_of_lt
  have := j.isLt
  omega

/-- Combining one triangular row is just a bit permutation and masked ANDs;
no arbitrary phase or exponentially large truth table is present. -/
def rowNetwork {b : ℕ} (j : Fin b) : BooleanNetwork b b :=
  vector (fun e => if j.val ≤ e.val ∧ e.val < b-1 then
    (bit (rowIndex j e)).band (bit j)
    else constant false)

lemma rowNetwork_count {b : ℕ} (j : Fin b) : (rowNetwork j).net.count = b := by
  rw [rowNetwork, count_vector]
  have h : ∀ e : Fin b, (if j.val ≤ e.val ∧ e.val < b-1 then
      (bit (rowIndex j e)).band (bit j)
      else constant false).net.count = 1 := by
    intro e
    by_cases he : j.val ≤ e.val ∧ e.val < b-1
    · rw [ite_eq_left he]; simp
    · rw [ite_eq_right he]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma rowNetwork_bit {b : ℕ} (j e : Fin b) (z : Bits b) :
    (rowNetwork j).eval z e = if j.val ≤ e.val ∧ e.val < b-1 then
      z (rowIndex j e) && z j else false := by
  rw [rowNetwork, eval_vector]
  split_ifs <;> simp_all

lemma rowNetwork_number {b : ℕ} (j : Fin b) (z : Bits b) :
    (bitsValue ((rowNetwork j).eval z)).toNat = rowShift j z := by
  classical
  rw [bitsValue_toNat]
  unfold rowShift
  simp_rw [rowNetwork_bit]
  have hand (a c : Bool) : (a && c).toNat = a.toNat*c.toNat := by
    cases a <;> cases c <;> rfl
  simp only [apply_ite Bool.toNat, Bool.toNat_false, mul_ite, mul_zero, hand, ← mul_assoc]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => rowIndex j e)
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rowIndex_val j e h.1]
    omega
  · intro e he f hf hef
    have h₁ := (Finset.mem_filter.mp he).2
    have h₂ := (Finset.mem_filter.mp hf).2
    have hv := congrArg Fin.val hef
    rw [rowIndex_val j e h₁.1, rowIndex_val j f h₂.1] at hv
    exact Fin.ext (by omega)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    let e : Fin b := ⟨b-1-i.val+j.val,by have := i.isLt; omega⟩
    have he : j.val ≤ e.val ∧ e.val < b-1 := by dsimp [e]; have := i.isLt; omega
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩, ?_⟩
    apply Fin.ext
    rw [rowIndex_val j e he.1]
    dsimp [e]
    have := i.isLt
    omega
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    rw [rowIndex_val j e h.1]
    have hw : b-1-(b-1+j.val-e.val)+j.val = e.val := by
      have := e.isLt
      omega
    rw [hw]

end ExactQuantumFactoring.Triangular


end

end OAI
