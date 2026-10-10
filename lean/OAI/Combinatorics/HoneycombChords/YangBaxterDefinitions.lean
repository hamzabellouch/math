import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! Local numerator matrices for the honeycomb Yang–Baxter identity.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

noncomputable def numerator (C A S x y ii : ℂ) (p q : Fin 3 × Fin 3) : ℂ :=
  let cc := (C*y-A*x)*S*(y-x)
  let aa := S*(C*y-A*x)
  let vv := (C*y-A*x)*x
  let dd := x*(C*x-A*y)
  let qq := S*(y+x)*(C*y+A*x)
  match p.1.val, p.2.val, q.1.val, q.2.val with
  | 0, 0, 0, 0 => cc
  | 2, 2, 2, 2 => cc
  | 0, 1, 0, 1 => vv
  | 1, 0, 1, 0 => vv
  | 2, 1, 2, 1 => vv
  | 1, 2, 1, 2 => vv
  | 0, 1, 1, 0 => aa
  | 1, 0, 0, 1 => aa
  | 2, 1, 1, 2 => aa
  | 1, 2, 2, 1 => aa
  | 0, 2, 0, 2 => dd
  | 0, 2, 1, 1 => x/2*(1-ii)
  | 0, 2, 2, 0 => cc-ii*dd
  | 1, 1, 0, 2 => x/2*(1+ii)
  | 1, 1, 1, 1 => qq
  | 1, 1, 2, 0 => x/2*(1-ii)
  | 2, 0, 0, 2 => cc+ii*dd
  | 2, 0, 1, 1 => x/2*(1+ii)
  | 2, 0, 2, 0 => dd
  | _, _, _, _ => 0

noncomputable def leftComponent (C A S x y z w ii : ℂ)
    (a b c d e f : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    numerator C A S (x*w-y*z) (y*w+x*z) ii (a,b) (j,k) *
    numerator C A S x y ii (j,c) (d,l) *
    numerator C A S z w ii (k,l) (e,f)

noncomputable def rightComponent (C A S x y z w ii : ℂ)
    (a b c d e f : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    numerator C A S z w ii (b,c) (k,l) *
    numerator C A S x y ii (a,l) (j,f) *
    numerator C A S (x*w-y*z) (y*w+x*z) ii (j,k) (d,e)

abbrev complexAdd (a b : ℂ) : ℂ := a+b
abbrev complexMul (a b : ℂ) : ℂ := a*b
abbrev complexPow (a : ℂ) (n : ℕ) : ℂ := a^n
lemma finThreeTwo : (2:Fin 3).val = 2 := rfl

end CriticalHoneycomb.Transfer.YangBaxter

end OAI
