import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Correct

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr

section
open Polynomial

 noncomputable def valuePolynomial : Expr → Polynomial ℕ
  | .const n => C n
  | .arg _ | .length => X
  | .bit _ | .zero _ => 1
  | .add a b => valuePolynomial a+valuePolynomial b
  | .sub a _ => valuePolynomial a
  | .mul a b => valuePolynomial a*valuePolynomial b
  | .sum b f => valuePolynomial b*(valuePolynomial f).comp (X+valuePolynomial b)

 theorem valuePolynomial_eval (e : Expr) (M : ℕ) :
    e.valuePolynomial.eval M = e.valueBudget M := by
  induction e generalizing M <;>
    simp_all [valuePolynomial, valueBudget, Polynomial.eval_comp]

 noncomputable def timePolynomial : Expr → Polynomial ℕ
  | .const n => C (n+1)
  | .arg _ => 5*X+2
  | .length => 5*X+6
  | .bit e => timePolynomial e+3*valuePolynomial e+X+7
  | .add a b | .sub a b => timePolynomial a+timePolynomial b+2*valuePolynomial b+1
  | .mul a b => timePolynomial a+timePolynomial b+
      valuePolynomial b*(5*valuePolynomial a+3)+1+2*valuePolynomial a+1+
      2*(valuePolynomial a*valuePolynomial b)+1
  | .zero a => timePolynomial a+2*valuePolynomial a+2
  | .sum b f => timePolynomial b+valuePolynomial b*
      ((timePolynomial f).comp (X+valuePolynomial b)+
        2*(valuePolynomial f).comp (X+valuePolynomial b)+3)+2*valuePolynomial b+2

 theorem timePolynomial_eval (e : Expr) (M : ℕ) :
    e.timePolynomial.eval M = e.timeBudget M := by
  induction e generalizing M <;>
    simp_all [timePolynomial, timeBudget, valuePolynomial_eval, Polynomial.eval_comp]

end

open scoped BigOperators
open Finset Command

 theorem correct_sum {b f : Expr} (hcb : Correct b) (hcf : Correct f) : Correct (.sum b f) := by
  intro vars k d M hv hc hb hi ha
  let args := fun i => d.reg (vars i)
  let B := b.eval d.input args
  let F := fun i => f.eval d.input (bind args i)
  let V := b.valueBudget M
  let W := f.valueBudget (M+V)
  let T := f.timeBudget (M+V)
  have hB : B ≤ V := b.eval_le d.input args M hi ha
  have hF : ∀ i < B, F i ≤ W := by
    intro i hi'
    apply f.eval_le
    · omega
    · intro j; cases j with
      | zero => dsimp [bind]; omega
      | succ j => exact (ha j).trans (by omega)
  let state : ℕ → Data ℕ := fun i =>
    ((d.set k (∑ j ∈ range (B-i), F j)).set (k+1) i).set (k+2) (B-i)
  have hz : ∀ r, k ≤ r → d.reg r = 0 := hc
  have hbnd := hcb vars (k+1) d M (fun i => by have := hv i; omega)
    (hc.mono (by omega)) hb hi ha
  have hstart : state B = d.set (k+1) B := by
    simp only [state, Nat.sub_self, range_zero, sum_empty]
    rw [Data.set_clean_zero hc le_rfl]
    exact Data.set_clean_zero ((hc.mono (by omega)).set_succ B) le_rfl
  have hloop : Within (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
      (.seq (move (k+3) k) (.inc (k+2))))) (state B) (state 0) (B*(T+2*W+3)+1) := by
    apply (Within.loop (k+1) _ state B (T+2*W+2))
    · intro i hi'
      simp [state, Data.set]
    · intro i hi'
      let j := B-(i+1)
      let e := decData (state (i+1)) (k+1)
      have hj : j < B := by dsimp [j]; omega
      have hindex : B-i = j+1 := by dsimp [j]; omega
      have heclean : e.Clean (k+3) := by
        intro r hr
        have h0 : r ≠ k := by omega
        have h1 : r ≠ k+1 := by omega
        have h2 : r ≠ k+2 := by omega
        simp [e, decData, state, Data.set, h0, h1, h2, hc r (by omega)]
      have henv : (fun u => e.reg (bind vars (k+2) u)) = bind args j := by
        funext u
        cases u with
        | zero => simp [e, decData, state, Data.set, bind, j]
        | succ u =>
          have h0 : vars u ≠ k := by have := hv u; omega
          have h1 : vars u ≠ k+1 := by have := hv u; omega
          have h2 : vars u ≠ k+2 := by have := hv u; omega
          simp [e, decData, state, Data.set, bind, args, h0, h1, h2]
      have heargs : ∀ u, e.reg (bind vars (k+2) u) ≤ M+V := by
        intro u
        change (fun u => e.reg (bind vars (k+2) u)) u ≤ M+V
        rw [henv]
        cases u with
        | zero => dsimp [bind]; omega
        | succ u => exact (ha u).trans (by omega)
      have hf := hcf (bind vars (k+2)) (k+3) e (M+V)
        (fun u => by cases u with
          | zero => dsimp [bind]; omega
          | succ u => dsimp [bind]; have := hv u; omega) heclean hb (by exact hi.trans (by omega)) heargs
      rw [henv] at hf
      change Within _ e (e.set (k+3) (F j)) T at hf
      have hm := Within.move (e.set (k+3) (F j)) (k+3) k (by omega)
      let out := (((e.set (k+3) (F j)).set (k+3) 0).set k
        ((e.set (k+3) (F j)).reg k+(e.set (k+3) (F j)).reg (k+3)))
      have hh := hf.seq (hm.seq (Within.inc out (k+2)))
      have hsum : (∑ u ∈ range (B-i), F u) = (∑ u ∈ range j, F u)+F j := by
        rw [hindex, sum_range_succ]
      have hout : incData out (k+2) = state i := by
        apply Data.ext
        · ext u
          have hz3 := hc (k+3) (by omega)
          by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;>
            by_cases h2 : u = k+2 <;> by_cases h3 : u = k+3 <;>
            simp [out, e, state, Data.set, incData, decData,
              h0, h1, h2, h3, j, hsum, hz3] <;> omega
        all_goals rfl
      rw [hout] at hh
      apply hh.mono
      simp only [Data.set_reg_same]
      have := hF j hj
      omega
  rw [hstart] at hloop
  have hclear := Within.clear (state 0) (k+2)
  have hout : (state 0).set (k+2) 0 = d.set k (∑ j ∈ range B, F j) := by
    dsimp only [state]
    rw [Data.set_set]
    apply Data.ext
    · ext u
      have hz1 := hc (k+1) (by omega)
      have hz2 := hc (k+2) (by omega)
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [Data.set, h0, h1, h2, hz1, hz2]
    all_goals rfl
  rw [hout] at hclear
  have hclear' : Within (clear (k+2)) (state 0) (d.set k (∑ j ∈ range B, F j)) (2*B+1) := by
    simpa [state, Data.set] using hclear
  have hh := hbnd.seq (hloop.seq hclear')
  apply hh.mono

  change _ ≤ b.timeBudget M+V*(T+2*W+3)+2*V+2
  have ht := Nat.mul_le_mul_right (T+2*W+3) hB
  omega

 theorem correct (e : Expr) : Correct e := by
  induction e with
  | const n => exact correct_const n
  | arg i => exact correct_arg i
  | length => exact correct_length
  | bit a ih => exact correct_bit ih
  | add a b ia ib => exact correct_add ia ib
  | sub a b ia ib => exact correct_sub ia ib
  | mul a b ia ib => exact correct_mul ia ib
  | zero a ih => exact correct_zero ih
  | sum b f ib iF => exact correct_sum ib iF

end IndependentSetsCut.CounterMachine.Expr

end OAI
