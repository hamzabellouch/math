import Mathlib
import OAI.Computability.QuantumFactoring.BooleanAlgebra

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

def any {n : ℕ} : List (BooleanNetwork n 1) → BooleanNetwork n 1
  | [] => constant false
  | c::cs => c.bor (any cs)

lemma any_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (any cs).eval x 0=true ↔ ∃ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [any]
  | cons c cs ih => simp [any,ih]

lemma any_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (any cs).net.count ≤ cs.length*(c+4)+1 := by
  induction cs with
  | nil => simp [any]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [any,count_bor,List.length_cons]
    nlinarith

def all {n : ℕ} : List (BooleanNetwork n 1) → BooleanNetwork n 1
  | [] => constant true
  | c::cs => c.band (all cs)

lemma all_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (all cs).eval x 0=true ↔ ∀ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [all]
  | cons c cs ih => simp [all,ih]

lemma all_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (all cs).net.count ≤ cs.length*(c+1)+1 := by
  induction cs with
  | nil => simp [all]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [all,count_band,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
