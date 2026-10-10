import OAI.Computability.MatchingCount.RawOptimizerDataCompiler

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly BinaryMatching.Raw.Compiler
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

@[fun_prop] theorem capacities_poly : Poly (fun z : ℕ×Matrix ℤ => capacities z.1 z.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×Matrix ℤ)×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then (get z.1.1.2 z.1.2 z.2).toNat else
    if decide (z.2<z.1.2) then (get z.1.1.2 z.2 z.1.2).toNat else 0) (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [capacities,decide_eq_true_eq])
@[fun_prop] theorem zeroRow_poly : Poly zeroRow := by
  unfold zeroRow
  apply Poly.pair
  · exact Poly.rawMatrix id (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem degreeRow_poly : Poly (fun z : ℕ×(ℕ×Bool) => degreeRow z.1 z.2.1 z.2.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×(ℕ×Bool))×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then
      if decide (z.1.2=z.1.1.2.1) || decide (z.2=z.1.1.2.1) then (if z.1.1.2.2 then (1:ℤ) else -1) else 0 else 0)
    (by fun_prop) (by fun_prop)
  have hh := Poly.pair _ (fun z : ℕ×(ℕ×Bool) => if z.2.2 then (-1:ℤ) else 1) h (by fun_prop)
  exact hh.congr (fun _ => by simp only [degreeRow,Bool.or_eq_true,decide_eq_true_eq])
@[fun_prop] theorem cutRow_poly : Poly (fun z : ℕ×Cut => cutRow z.1 z.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×Cut)×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then
      if (mem z.1.1.2 z.1.2 && !mem z.1.1.2 z.2) || (mem z.1.1.2 z.2 && !mem z.1.1.2 z.1.2) then (-1:ℤ) else 0 else 0)
    (by fun_prop) (by fun_prop)
  exact (Poly.pair _ (fun _ => (1:ℤ)) h (by fun_prop)).congr (fun _ => by simp only [cutRow,decide_eq_true_eq])
@[fun_prop] theorem rows_poly : Poly (fun z : ℕ×Matrix ℤ => rows z.1 z.2) := by
  have hd : Poly (fun z : ℕ×Matrix ℤ => (List.range z.1).flatMap (fun v => [degreeRow z.1 v true,degreeRow z.1 v false])) :=
    Poly.flatMapWith (fun z : ℕ×Matrix ℤ => List.range z.1)
      (fun z : (ℕ×Matrix ℤ)×ℕ => [degreeRow z.1.1 z.2 true,degreeRow z.1.1 z.2 false]) (by fun_prop) (by fun_prop)
  unfold rows
  fun_prop
@[fun_prop] theorem selectedRow_poly : Poly (fun z : ℕ×(ℕ×Matrix ℤ) => selectedRow z.1 z.2.1 z.2.2) := by
  let arg (z : ℕ×(ℕ×Matrix ℤ)) := (rows z.1 z.2.2).argmax (rowNumerator z.2.1 z.2.2)
  have ha : Poly arg :=
    Poly.comp _ (fun z : ℕ×(ℕ×Matrix ℤ) => (z,rows z.1 z.2.2))
      (Poly.listArgmaxParam Poly.intLT (fun z : (ℕ×(ℕ×Matrix ℤ))×Row => rowNumerator z.1.2.1 z.1.2.2 z.2)
        (by fun_prop)) (by fun_prop)
  have h : Poly (fun z : ℕ×(ℕ×Matrix ℤ) => if (arg z).isSome then (arg z).getD (default:Row) else zeroRow z.1) := by fun_prop
  exact h.congr (fun z => by change _=(arg z).getD _; cases arg z <;> rfl)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
