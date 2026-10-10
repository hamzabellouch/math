import Mathlib
import OAI.Computability.MaxCut.Estimates.Divides

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
namespace Expr

def framedLen (n : Expr) : Expr := .add (.mul (.const 2) (size n)) (.const 1)
def framedBit (n i : Expr) : Expr := cond (lt i (.mul (.const 2) (size n)))
  (cond (equal (remainder i (.const 2)) (.const 0)) (.const 1)
    (digit n (quotient i (.const 2)))) (.const 0)

@[simp] theorem framedLen_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (framedLen n).eval input args = 2*(n.eval input args).size+1 := by
  simp [framedLen, eval]

 theorem framedBit_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (framedBit n i).eval input args =
      if i.eval input args < 2*(n.eval input args).size then
        if i.eval input args % 2 = 0 then 1 else n.eval input args / 2^(i.eval input args/2) % 2
      else 0 := by
  simp only [framedBit, cond_eval, lt_eval, eval, equal_eval, remainder_eval, size_eval]
  by_cases hi : i.eval input args < 2*(n.eval input args).size
  · simp only [hi, ↓reduceIte]
    by_cases h2 : i.eval input args % 2 = 0
    · simp [h2]
    · simp only [h2, ↓reduceIte]
      have hsmall : (quotient i (.const 2)).eval input args < (n.eval input args).size := by
        simp only [quotient_eval, eval]; omega
      simpa [quotient_eval, eval] using digit_eval n (quotient i (.const 2)) input args hsmall
  · simp [hi]
end Expr

def frame : List Bool → List Bool
  | [] => [false]
  | b::s => true::b::frame s

@[simp] theorem frame_length (s : List Bool) : (frame s).length = 2*s.length+1 := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [frame, ih]; omega

 theorem frame_get (s : List Bool) (i : ℕ) :
    ((frame s)[i]?).getD false =
      if i<2*s.length then if i%2=0 then true else (s[i/2]?).getD false else false := by
  induction s generalizing i with
  | nil => simp [frame]
  | cons b s ih =>
    rcases i with _|_ | i
    · simp [frame]
    · simp [frame]; omega
    · simp only [frame, List.getElem?_cons_succ, ih, List.length_cons]
      have hdiv : (i+1+1)/2 = i/2+1 := by omega
      have hmod : (i+1+1)%2 = i%2 := by omega
      have hlt : i+1+1 < 2*(s.length+1) ↔ i<2*s.length := by omega
      simp only [hdiv,hmod,hlt,List.getElem?_cons_succ]

 theorem frame_bits_get (n i : ℕ) :
    ((frame n.bits)[i]?).getD false =
      decide ((if i<2*n.size then if i%2=0 then 1 else n/2^(i/2)%2 else 0 : ℕ) ≠ 0) := by
  rw [frame_get, Nat.size_eq_bits_len]
  by_cases hi : i<2*n.size <;> by_cases h2 : i%2=0 <;> simp only [hi,h2,↓reduceIte]
  · rfl
  · change n.bits.getI (i/2) = _
    rw [← Nat.testBit_eq_inth, Nat.testBit_eq_decide_div_mod_eq]
    simp only [Nat.mod_two_ne_zero]
  · rfl
  · rfl

end OptimalMaxCut.CounterMachine

end

end OAI
