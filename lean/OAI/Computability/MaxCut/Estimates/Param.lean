import Mathlib
import OAI.Computability.MaxCut.Arithmetic.Prime

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset CounterMachine.Expr
attribute [local instance] Classical.propDecidable

def param (q K : ℕ) (s : List Bool) : ℕ := Unweighted.searchPrime (K*(vertices s*2^q+1)^2)
def size (q K : ℕ) (s : List Bool) : ℕ := vertices s*2^q*(param q K s)^6
def scale (q K : ℕ) (s : List Bool) : ℕ := (param q K s)^12
def coordinate (p i k : ℕ) : ℕ := (i % p^6)/p^k % p
def pairing (p i j : ℕ) : ℕ := (∑ k : Fin 6, coordinate p i k.val * coordinate p j k.val)%p
noncomputable def adjacency (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (s : List Bool) (i j : ℕ) : ℕ :=
  let p := param q L s
  if i/p^6=j/p^6 then 0 else
    ∑ r ∈ range (p*weights q t ht K s (i/p^6) (j/p^6)/gridSize q K s),
      if r%p=pairing p i j then 1 else 0

def frameValue (n i : ℕ) : ℕ :=
  if i<2*n.size then if i%2=0 then 1 else n/2^(i/2)%2 else 0
def length (q L : ℕ) (s : List Bool) : ℕ :=
  (2*(size q L s).size+1)+(2*(scale q L s).size+1)+(size q L s)^2
noncomputable def entry (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (s : List Bool) (i : ℕ) : ℕ :=
  let n := size q L s
  let d := 2*n.size+1
  let e := 2*(scale q L s).size+1
  if i<d then frameValue n i else if i<d+e then frameValue (scale q L s) (i-d) else
    adjacency q t ht K L s ((i-d-e)/n) ((i-d-e)%n)

namespace Rep
open CounterMachine.Expr.Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem param (q K : ℕ) : Represented (fun s _ => RawGrid.param q K s) :=
  searchPrime ((Represented.const K).mul (((vertices.mul (Represented.const (2^q))).add (Represented.const 1)).pow 2))
theorem size (q K : ℕ) : Represented (fun s _ => RawGrid.size q K s) :=
  (vertices.mul (Represented.const (2^q))).mul ((param q K).pow 6)
theorem scale (q K : ℕ) : Represented (fun s _ => RawGrid.scale q K s) := (param q K).pow 12
theorem coordinate (k : ℕ) (hp : Represented f) (hi : Represented g) :
    Represented (fun s a => RawGrid.coordinate (f s a) (g s a) k) :=
  ((hi.mod (hp.pow 6)).div (hp.pow k)).mod hp
theorem pairing (hp : Represented f) (hi : Represented g) (hj : Represented h) :
    Represented (fun s a => RawGrid.pairing (f s a) (g s a) (h s a)) :=
  (Represented.finiteSum (fun k : Fin 6 => (coordinate k.val hp hi).mul (coordinate k.val hp hj))).mod hp
theorem adjacency (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (hi : Represented f) (hj : Represented g) :
    Represented (fun s a => RawGrid.adjacency q t ht K L s (f s a) (g s a)) := by
  let hp := param q L
  let hu := hi.div (hp.pow 6)
  let hv := hj.div (hp.pow 6)
  apply iteEq hu hv (Represented.const 0)
  apply bounded ((hp.mul (weights q t ht K hu hv)).div (gridSize q K))
  exact eq ((Represented.arg 0).mod hp) (pairing hp (hi.rename Nat.succ) (hj.rename Nat.succ))
theorem frameValue (hn : Represented f) (hi : Represented g) :
    Represented (fun s a => RawGrid.frameValue (f s a) (g s a)) := framedBit hn hi
theorem length (q L : ℕ) : Represented (fun s _ => RawGrid.length q L s) :=
  ((framedLen (size q L)).add (framedLen (scale q L))).add ((size q L).pow 2)
theorem entry (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (hi : Represented f) : Represented (fun s a => RawGrid.entry q t ht K L s (f s a)) := by
  let hn := size q L
  let hd := framedLen hn
  let he := framedLen (scale q L)
  apply iteLt hi hd (frameValue hn hi)
  apply iteLt hi (hd.add he) (frameValue (scale q L) (hi.sub hd))
  exact adjacency q t ht K L (((hi.sub hd).sub he).div hn) (((hi.sub hd).sub he).mod hn)
end Rep
end OptimalMaxCut.RawGrid

end

end OAI
