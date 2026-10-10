import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.BitValue

namespace OAI

namespace IndependentSetsCut.CounterMachine
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

end IndependentSetsCut.CounterMachine

namespace IndependentSetsCut.CounterMachine.Expr

section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def listSum {I : Type} (l : List I) (f : I → Expr) : Expr :=
  l.foldr (fun i s => .add (f i) s) (.const 0)
@[simp] theorem listSum_eval {I : Type} (l : List I) (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (listSum l f).eval input args = (l.map (fun i => (f i).eval input args)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (f i).eval input args + (listSum l f).eval input args = _
    simp [ih]

noncomputable def finiteSum {I : Type} [Fintype I] (f : I → Expr) : Expr :=
  listSum Finset.univ.toList f
@[simp] theorem finiteSum_eval {I : Type} [Fintype I] (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (finiteSum f).eval input args = ∑ i, (f i).eval input args := by
  simp [finiteSum]

def least (bound predicate : Expr) : Expr :=
  .sum bound (.mul (.arg 0) (.mul (positive predicate)
    (.zero (.sum (.arg 0) (positive (predicate.rename (fun
      | 0 => 0
      | j+1 => j+2)))))))

 theorem least_eval (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (least bound predicate).eval input args =
      ∑ i ∈ range (bound.eval input args),
        if predicate.eval input (bind args i) ≠ 0 ∧
          ∀ j < i, predicate.eval input (bind args j) = 0 then i else 0 := by
  have hb (i j : ℕ) : (fun k => bind (bind args i) j (match k with
      | 0 => 0
      | k+1 => k+2)) = bind args j := by
    funext k; cases k <;> rfl
  simp only [least, eval, positive_eval, rename_eval, hb]
  apply sum_congr rfl
  intro i hi
  have hz : (∑ j ∈ range i,
      if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0) = 0 ↔
      ∀ j < i, predicate.eval input (bind args j)=0 := by
    simp only [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _), mem_range]
    simp
  change i * ((if predicate.eval input (bind args i) ≠ 0 then 1 else 0) *
    (if (∑ j ∈ range i, if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0)=0 then 1 else 0)) = _
  simp only [hz]
  rw [indicator_and]
  split_ifs <;> simp

end

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem least_eq (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) (k : ℕ)
    (hk : k < bound.eval input args)
    (hp : predicate.eval input (bind args k) ≠ 0)
    (he : ∀ j < k, predicate.eval input (bind args j) = 0) :
    (least bound predicate).eval input args = k := by
  rw [least_eval, sum_eq_single_of_mem k (mem_range.mpr hk)]
  · exact ite_eq_left ⟨hp, he⟩
  · intro j hj hne
    by_cases h : j < k
    · simp [he j h]
    · have hkj : k < j := by omega
      split_ifs with hgood
      · exact False.elim (hp (hgood.2 k hkj))
      · rfl

end IndependentSetsCut.CounterMachine.Expr

end OAI
