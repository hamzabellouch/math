import Mathlib
import OAI.Combinatorics.KMedian.Machines.FiniteCompiler
import OAI.Combinatorics.KMedian.Machines.ListCompiler

namespace OAI

section Inline_PCPUnaryPolynomial
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic Polynomial
open scoped Classical

lemma unitList_eq_length {xs ys : List Unit} (h : xs.length=ys.length) : xs=ys :=
  List.ext_getElem h (by intros; exact Subsingleton.elim _ _)
noncomputable def unaryPower : ℕ → List Unit → List Unit
  | 0, _ => [()]
  | n+1, xs => xs.flatMap (fun _ => unaryPower n xs)
lemma unaryPower_length (n : ℕ) (xs : List Unit) : (unaryPower n xs).length=xs.length^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unaryPower,length_flatMap_uniform xs _ (xs.length^n) (by intros; exact ih),pow_succ']
lemma poly_unaryPower (n : ℕ) : Poly (unaryPower n) := by
  induction n with
  | zero => exact Automatic.Poly.const _
  | succ n ih =>
    exact Poly.list_flatMap (ih.comp Poly.fst) Poly.identity
lemma poly_unaryPolynomial (p : Polynomial ℕ) :
    Poly (fun xs : List Unit => List.replicate (p.eval xs.length) ()) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    apply poly_congr (Poly.list_append.comp (Poly.pair hp hq))
    intro xs
    simp only [eval_add,List.replicate_add]
  | monomial n a =>
    have hh : Poly (fun xs : List Unit => (unaryPower n xs).flatMap (fun _ => List.replicate a ())) :=
      Poly.list_flatMap (Automatic.Poly.const _) (poly_unaryPower n)
    apply poly_congr hh
    intro xs
    apply unitList_eq_length
    rw [length_flatMap_uniform _ _ a (by intros; simp),List.length_replicate,
      unaryPower_length,eval_monomial,Nat.mul_comm]
end MetricKMedian.PCP.Compiler

end Inline_PCPUnaryPolynomial

end OAI
