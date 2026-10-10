import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryIterations
import OAI.Combinatorics.KMedian.Expanders.ExpanderGuard

namespace OAI

section Inline_PCPExpanderCompiler
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable Binary Binary.Automatic Polynomial
open scoped Classical

noncomputable def sizePoly : Polynomial ℕ :=
  2*(X+1)+1+(C growth*(X+1)) *
    (2*(C (Fintype.card Degree)*(2*(2*(C growth*(X+1)+1)+1+C (codeBound (D := Degree)))+1))+1)
lemma reachable_size (xs : List Unit) (i : ℕ) :
    (enc (guarded^[i] (xs.length,initial))).length ≤ sizePoly.eval (enc xs).length := by
  rw [iterate_guarded]
  have ht := size_bound (sequence_wellFormed xs.length i) _ (sequence_length xs.length i)
  have hn : xs.length ≤ (enc xs).length := EncodedList.length_le _ _
  have hb : xs.length.bits.length ≤ xs.length+1 :=
    NatBinary.length_le_height (Nat.lt_two_pow_self (n := xs.length)).le
  change (encodePair Nat.bits enc (sequence xs.length i)).length ≤ _
  rw [encodePair_length]
  change 2*xs.length.bits.length+1+(enc (sequence xs.length i).2).length ≤ _
  apply (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb) 1) ht).trans
  unfold sizeBound sizePoly
  simp only [eval_add,eval_mul,eval_X,eval_C,eval_one,eval_ofNat]
  gcongr
lemma poly_initialState : Poly (fun xs : List Unit => (xs.length,initial)) :=
  Poly.pair Poly.list_length (Automatic.Poly.const _)
lemma poly_steps : Poly (fun xs : List Unit => xs.length+2) := by fun_prop
lemma poly_trajectory : Poly (fun xs : List Unit =>
    Iteration.iterates guarded (xs.length,initial) (xs.length+2)) := by
  refine ⟨poly_guarded.program.iteratesFrom poly_initialState.program poly_steps.program
    (0,initial) (X+2) sizePoly ?_ ?_⟩
  · intro xs
    have h : xs.length ≤ (enc xs).length := EncodedList.length_le _ _
    simpa only [eval_add,eval_X,eval_ofNat] using Nat.add_le_add_right h 2
  · intro xs i hi
    exact reachable_size xs i
lemma poly_generate : Poly generate := by
  have hi : Poly (fun xs : List Unit => xs.length+1) := by fun_prop
  have hg := Poly.list_getD_comp (0,initial) poly_trajectory hi
  apply poly_congr (Poly.snd.comp hg)
  intro xs
  change ((Iteration.iterates guarded (xs.length,initial) (xs.length+2))[xs.length+1]?.getD
    (0,initial)).2=generate xs
  rw [Iteration.iterates_eq]
  simp only [List.getElem?_map,List.getElem?_range,show xs.length+1<xs.length+2 by omega,
    Option.map_some,Option.getD_some,generate]
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderCompiler

end OAI
